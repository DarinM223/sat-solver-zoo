use crate::types::{Assignments, Clause, ClauseIndex, Formula, Lit, Var};
use rand::seq::IteratorRandom;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

pub struct Watcher {
    lit_to_clauses: HashMap<Lit, Vec<ClauseIndex>>,
    clause_to_lits: HashMap<ClauseIndex, Vec<Lit>>,
}

impl Watcher {
    pub fn new(formula: &Formula) -> Self {
        let mut lit_to_clauses: HashMap<Lit, Vec<ClauseIndex>> = HashMap::new();
        let mut clause_to_lits: HashMap<ClauseIndex, Vec<Lit>> = HashMap::new();
        for (clause_idx, clause) in formula.clauses.iter_with_clause_indices() {
            if clause.len() == 1 {
                let key = clause.lits.iter().next().unwrap();
                append_multimap(&mut lit_to_clauses, key, clause_idx);
                append_multimap(&mut clause_to_lits, &clause_idx, *key);
            } else {
                let [lit1, lit2] = clause.lits.iter().take(2).cloned().collect::<Vec<_>>()[..]
                else {
                    panic!("Clause should have either 1 or 2 literals in it, unexpected");
                };
                append_multimap(&mut lit_to_clauses, &lit1, clause_idx);
                append_multimap(&mut clause_to_lits, &clause_idx, lit1);
                append_multimap(&mut lit_to_clauses, &lit2, clause_idx);
                append_multimap(&mut clause_to_lits, &clause_idx, lit2);
            }
        }
        Watcher {
            lit_to_clauses,
            clause_to_lits,
        }
    }

    pub fn get_clauses(&self, lit: &Lit) -> impl Iterator<Item = ClauseIndex> + use<'_> {
        self.lit_to_clauses
            .get(lit)
            .into_iter()
            .flat_map(|nodes| nodes.iter().cloned())
    }

    pub fn get_lits(&self, clause_idx: ClauseIndex) -> impl Iterator<Item = Lit> {
        self.clause_to_lits
            .get(&clause_idx)
            .into_iter()
            .flat_map(|nodes| nodes.iter().cloned())
    }

    pub fn has_lit(&self, clause_idx: ClauseIndex, lit: &Lit) -> bool {
        match self.clause_to_lits.get(&clause_idx) {
            Some(clauses) => clauses.contains(lit),
            None => false,
        }
    }

    pub fn rewatch(&mut self, clause_idx: ClauseIndex, old: &Lit, new: &Lit) {
        if let Some(lits) = self.clause_to_lits.get_mut(&clause_idx) {
            if let Some(pos) = lits.iter().position(|x| x == old) {
                lits.remove(pos);
            }
            lits.push(*new);
        }
        if let Some(clauses) = self.lit_to_clauses.get_mut(old)
            && let Some(pos) = clauses.iter().position(|x| *x == clause_idx)
        {
            clauses.remove(pos);
        }
        self.lit_to_clauses
            .get_mut(new)
            .get_or_insert(&mut Vec::new())
            .push(clause_idx);
    }

    pub fn add(&mut self, clause_idx: ClauseIndex, lit: &Lit) {
        append_multimap(&mut self.clause_to_lits, &clause_idx, *lit);
        append_multimap(&mut self.lit_to_clauses, lit, clause_idx);
    }
}

fn append_multimap<K: Eq + Hash, V>(map: &mut HashMap<K, Vec<V>>, k: &K, v: V) {
    map.get_mut(k).get_or_insert(&mut Vec::new()).push(v);
}

impl Formula {
    pub fn pick_branching_variable(&self, assignments: &Assignments) -> (Var, bool) {
        let mut rng = rand::rng();
        let var = self
            .vars
            .iter()
            .filter(|&&var| !assignments.contains_var(var))
            .choose(&mut rng)
            .expect("No unassigned variable");
        let val = rand::random_bool(0.5);
        (*var, val)
    }
}

impl Assignments {
    pub fn satisfy(&self, formula: &Formula) -> bool {
        formula
            .clauses
            .iter()
            .all(|clause| clause.iter().any(|lit| self.value(*lit) == Some(true)))
    }
}

pub fn add_learnt_clause(
    watcher: &mut Watcher,
    formula: &mut Formula,
    clause: Clause,
    assignments: &Assignments,
) -> ClauseIndex {
    let mut lits = clause.iter().cloned().collect::<Vec<_>>();
    let clause_idx = formula.clauses.push(clause);

    // add recently assigned literals to watcher
    lits.sort_by(|lit1, lit2| {
        let v1 = assignments.decision_level(lit1.var);
        let v2 = assignments.decision_level(lit2.var);
        v1.cmp(&v2).reverse()
    });
    for lit in lits {
        if watcher.get_lits(clause_idx).count() >= 2 {
            break;
        }
        watcher.add(clause_idx, &lit);
    }
    clause_idx
}

pub fn cdcl_solve(formula: &mut Formula) -> Option<Assignments> {
    let mut watcher = Watcher::new(formula);
    let mut to_propagate = Vec::new();
    let mut assignments = Assignments::new(formula.max_var_size());

    for (clause_idx, clause) in formula
        .clauses
        .iter_with_clause_indices()
        .filter(|(_, clause)| clause.len() == 1)
    {
        let lit = clause.iter().next().unwrap();
        if assignments.contains_var(lit.var) {
            assignments.assign(lit.var, !lit.neg, Some(clause_idx));
            to_propagate.push(*lit);
        }
    }

    match unit_propagation(&mut watcher, formula, &mut assignments, &mut to_propagate) {
        Reason::Conflict(_) => return None,
        Reason::Unresolved => {}
    };

    while !formula.all_variables_assigned(&assignments) {
        let (mut var, mut val) = formula.pick_branching_variable(&assignments);
        let mut learnt_clause = None;
        assignments.curr_decision_level += 1;
        loop {
            assignments.assign(var, val, learnt_clause);
            to_propagate.clear();
            to_propagate.push(Lit { var, neg: !val });

            let clause = match unit_propagation(
                &mut watcher,
                formula,
                &mut assignments,
                &mut to_propagate,
            ) {
                Reason::Conflict(clause_index) => clause_index,
                Reason::Unresolved => break,
            };

            let (backtrack_level, clause) =
                conflict_analysis(formula, formula.clauses.get(clause).unwrap(), &assignments)?;
            let next_unit_literal = *clause
                .iter()
                .find(|lit| !assignments.contains_var(lit.var))
                .expect("Learned clause must be a unit clause");
            learnt_clause = Some(add_learnt_clause(
                &mut watcher,
                formula,
                clause,
                &assignments,
            ));
            assignments.backtrack(backtrack_level);
            assignments.curr_decision_level = backtrack_level;

            // Learned clause must be a unit clause, so run unit propagation again.
            (var, val) = (next_unit_literal.var, !next_unit_literal.neg);
        }
    }

    Some(assignments)
}

pub enum Reason {
    Conflict(ClauseIndex),
    Unresolved,
}

pub fn unit_propagation(
    watcher: &mut Watcher,
    formula: &Formula,
    assignments: &mut Assignments,
    to_propagate: &mut Vec<Lit>,
) -> Reason {
    while let Some(ref watching_lit) = to_propagate.pop().map(|lit| lit.neg()) {
        // Collect into a Vec to avoid the lifetime conflict with rewatch.
        let watching_clauses = watcher.get_clauses(watching_lit).collect::<Vec<_>>();
        for watching_clause in watching_clauses {
            let mut found_rewatch = false;
            for lit in formula.clauses.get(watching_clause).unwrap().iter() {
                if watcher.has_lit(watching_clause, lit) || assignments.value(*lit) == Some(false) {
                    continue;
                }

                found_rewatch = true;
                watcher.rewatch(watching_clause, watching_lit, lit);
                break;
            }
            if !found_rewatch {
                let watching_lits = watcher.get_lits(watching_clause).collect::<Vec<_>>();
                if watching_lits.len() == 1 {
                    return Reason::Conflict(watching_clause);
                }
                let other = if watching_lits[1] == *watching_lit {
                    watching_lits[0]
                } else {
                    watching_lits[1]
                };

                if !assignments.contains_var(other.var) {
                    assignments.assign(other.var, !other.neg, Some(watching_clause));
                    to_propagate.push(other);
                } else if assignments.value(other) == Some(true) {
                    continue;
                } else {
                    return Reason::Conflict(watching_clause);
                }
            }
        }
    }
    Reason::Unresolved
}

pub fn resolve(a: &Clause, b: &Clause, var: Var) -> Clause {
    // `|` is set union, `-` is set difference
    Clause {
        lits: &(&a.lits | &b.lits)
            - &HashSet::from([Lit { var, neg: true }, Lit { var, neg: false }]),
    }
}

/// Returns backtrack level and resolved clause.
pub fn conflict_analysis(
    formula: &Formula,
    clause: &Clause,
    assignments: &Assignments,
) -> Option<(u32, Clause)> {
    if assignments.curr_decision_level == 0 {
        return None;
    }
    let only_curr_decision_level =
        |lit: &&Lit| assignments.decision_level(lit.var) == Some(assignments.curr_decision_level);

    let mut clause = clause.clone();
    let mut literals = clause.lits.iter().filter(only_curr_decision_level);
    while literals.clone().count() != 1 {
        let lit = literals
            .find(|lit| assignments.antecedent(lit.var).is_some())
            .expect("Couldn't find a variable in the current decision level with an antecedent");
        let antecedent = assignments.antecedent(lit.var).unwrap();
        clause = resolve(&clause, formula.clauses.get(antecedent).unwrap(), lit.var);
        literals = clause.lits.iter().filter(only_curr_decision_level);
    }

    let mut decision_levels = clause
        .iter()
        .flat_map(|lit| assignments.decision_level(lit.var))
        .collect::<Vec<_>>();
    decision_levels.sort();
    if decision_levels.len() <= 1 {
        Some((0, clause))
    } else {
        Some((decision_levels[decision_levels.len() - 2], clause))
    }
}
