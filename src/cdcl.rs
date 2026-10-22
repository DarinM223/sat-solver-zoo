use crate::types::{Assignments, Clause, ClauseIndex, ClauseStore, Formula, Lit, LitStore, Var};
use rand::seq::IteratorRandom;
use std::collections::HashSet;

pub trait Append<K, V> {
    fn append(&mut self, k: K, v: V);
}

impl Append<Lit, ClauseIndex> for LitStore<Vec<ClauseIndex>> {
    fn append(&mut self, k: Lit, v: ClauseIndex) {
        match self.get_mut(&k) {
            Some(clauses) => clauses.push(v),
            None => {
                self.push();
                self.append(k, v);
            }
        }
    }
}

impl Append<ClauseIndex, Lit> for ClauseStore<Vec<Lit>> {
    fn append(&mut self, k: ClauseIndex, v: Lit) {
        match self.get_mut(&k) {
            Some(lits) => lits.push(v),
            None => {
                self.push(Vec::new());
                self.append(k, v);
            }
        }
    }
}

pub struct Watcher {
    lit_to_clauses: LitStore<Vec<ClauseIndex>>,
    clause_to_lits: ClauseStore<Vec<Lit>>,
}

impl Watcher {
    pub fn new(formula: &Formula) -> Option<Self> {
        let mut lit_to_clauses: LitStore<Vec<ClauseIndex>> =
            LitStore::preallocated(formula.max_var_size());
        let mut clause_to_lits: ClauseStore<Vec<Lit>> =
            ClauseStore::preallocated(formula.clauses.len());
        for (clause_idx, clause) in formula.clauses.iter_with_clause_indices() {
            if clause.len() == 1 {
                let key = clause.iter().next().unwrap();
                lit_to_clauses.append(*key, clause_idx);
                clause_to_lits.append(clause_idx, *key);
            } else {
                let [lit1, lit2] = clause.iter().take(2).cloned().collect::<Vec<_>>()[..] else {
                    // Expect at least one or two literals in clause.
                    return None;
                };
                lit_to_clauses.append(lit1, clause_idx);
                clause_to_lits.append(clause_idx, lit1);
                lit_to_clauses.append(lit2, clause_idx);
                clause_to_lits.append(clause_idx, lit2);
            }
        }
        Some(Watcher {
            lit_to_clauses,
            clause_to_lits,
        })
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
        self.lit_to_clauses.append(*new, clause_idx);
    }

    pub fn add(&mut self, clause_idx: ClauseIndex, lit: Lit) {
        self.clause_to_lits.append(clause_idx, lit);
        self.lit_to_clauses.append(lit, clause_idx);
    }
}

impl Formula {
    pub fn pick_branching_variable(&self, assignments: &Assignments) -> (Var, bool) {
        let mut rng = rand::rng();
        let var = self
            .vars()
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
        watcher.add(clause_idx, lit);
    }
    clause_idx
}

pub fn cdcl_solve(formula: &mut Formula) -> Option<Assignments> {
    let mut to_propagate = Vec::new();
    let mut watcher = Watcher::new(formula)?;
    let mut assignments = Assignments::new(formula.max_var_size());

    for (clause_idx, clause) in formula
        .clauses
        .iter_with_clause_indices()
        .filter(|(_, clause)| clause.len() == 1)
    {
        let lit = clause.iter().next().unwrap();
        if !assignments.contains_var(lit.var) {
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
                conflict_analysis(formula, formula.clauses.get(&clause).unwrap(), &assignments)?;

            let clause = add_learnt_clause(&mut watcher, formula, clause, &assignments);
            learnt_clause = Some(clause);
            assignments.backtrack(backtrack_level);
            assignments.curr_decision_level = backtrack_level;

            let next_unit_literal = formula.clauses[clause]
                .iter()
                .find(|lit| !assignments.contains_var(lit.var))
                .expect("Learned clause must be a unit clause");

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
            for lit in formula.clauses.get(&watching_clause).unwrap().iter() {
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
    let mut seen = HashSet::with_capacity(a.len() + b.len());
    let mut lits = Vec::with_capacity(a.len() + b.len());

    for &lit in a.iter().chain(b.iter()) {
        if lit.var != var && seen.insert(lit) {
            lits.push(lit);
        }
    }

    Clause::from_unique_lits(lits)
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
    loop {
        let (count, pivot) = clause.iter().filter(only_curr_decision_level).fold(
            (0, None),
            |(count, pivot), lit| {
                (
                    count + 1,
                    pivot.or_else(|| {
                        assignments
                            .antecedent(lit.var)
                            .map(|antecedent| (lit, antecedent))
                    }),
                )
            },
        );
        if count == 1 {
            break;
        }
        let (lit, antecedent) = pivot
            .expect("Couldn't find a variable in the current decision level with an antecedent");
        clause = resolve(&clause, &formula.clauses[antecedent], lit.var);
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

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_sat(input: &str) {
        let mut formula = Formula::from_dimacs_cnf(input);
        let assignments =
            cdcl_solve(&mut formula).unwrap_or_else(|| panic!("expected SAT:\n{input}"));
        assert!(
            assignments.satisfy(&formula),
            "solver returned an assignment that does not satisfy:\n{input}"
        );
    }

    fn assert_unsat(input: &str) {
        let mut formula = Formula::from_dimacs_cnf(input);
        assert!(
            cdcl_solve(&mut formula).is_none(),
            "expected UNSAT:\n{input}"
        );
    }

    #[test]
    fn empty_formula_is_sat() {
        assert_sat("p cnf 0 0\n");
    }

    #[test]
    fn empty_clause_is_unsat() {
        // A zero immediately ends a clause, making this one empty.
        assert_unsat("p cnf 0 1\n0\n");
    }

    #[test]
    fn unit_clause_forces_its_literal() {
        let mut formula = Formula::from_dimacs_cnf("p cnf 1 1\n1 0\n");
        let assignments = cdcl_solve(&mut formula).expect("expected SAT");

        assert_eq!(assignments.value(Lit::from_int(1)), Some(true));
        assert!(assignments.satisfy(&formula));
    }

    #[test]
    fn contradictory_unit_clauses_are_unsat() {
        assert_unsat("p cnf 1 2\n1 0\n-1 0\n");
    }

    #[test]
    fn unit_propagation_chain_is_satisfied() {
        // 1 forces 2, which forces 3.
        let mut formula = Formula::from_dimacs_cnf("p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n");
        let assignments = cdcl_solve(&mut formula).expect("expected SAT");

        assert_eq!(assignments.value(Lit::from_int(1)), Some(true));
        assert_eq!(assignments.value(Lit::from_int(2)), Some(true));
        assert_eq!(assignments.value(Lit::from_int(3)), Some(true));
        assert!(assignments.satisfy(&formula));
    }

    #[test]
    fn propagation_detects_conflicting_units() {
        // 1 forces 2, while the final clause requires 2 to be false.
        assert_unsat("p cnf 2 3\n1 0\n-1 2 0\n-2 0\n");
    }

    #[test]
    fn clauses_can_span_lines_and_comments_are_ignored() {
        let input = "c a comment\np cnf 2 2\n1\n-2 0\n2 0\n";
        assert_sat(input);
    }

    #[test]
    fn tautological_clause_is_satisfiable() {
        assert_sat("p cnf 1 1\n1 -1 0\n");
    }

    #[test]
    fn duplicate_literal_clause_is_satisfiable() {
        assert_sat("p cnf 1 1\n1 1 0\n");
    }

    #[test]
    fn conflicting_clauses_exercise_learning_and_backtracking() {
        // These four clauses exclude all four assignments to variables 1 and 2.
        assert_unsat(
            "p cnf 2 4\n\
             1 2 0\n\
             -1 2 0\n\
             1 -2 0\n\
             -1 -2 0\n",
        );
    }

    #[test]
    fn root_level_unit_clause_is_assigned_at_level_zero() {
        let mut formula = Formula::from_dimacs_cnf("p cnf 1 1\n-1 0\n");
        let assignments = cdcl_solve(&mut formula).expect("expected SAT");
        let unit = Lit::from_int(-1);

        assert_eq!(assignments.value(unit), Some(true));
        assert_eq!(assignments.decision_level(unit.var), Some(0));
        assert!(assignments.antecedent(unit.var).is_some());
    }

    #[test]
    fn backtracking_keeps_assignments_at_the_target_level() {
        let mut assignments = Assignments::new(3);
        let x1 = Lit::from_int(1).var;
        let x2 = Lit::from_int(2).var;

        assignments.curr_decision_level = 1;
        assignments.assign(x1, true, None);
        assignments.curr_decision_level = 2;
        assignments.assign(x2, false, None);

        assignments.backtrack(1);

        assert_eq!(assignments.value_var(x1), Some(true));
        assert_eq!(assignments.value_var(x2), None);
        assert_eq!(assignments.num_assigned_vars(), 1);
    }

    #[test]
    fn rewatch_moves_a_literal_watch_without_affecting_other_clauses() {
        let formula = Formula::from_dimacs_cnf(
            "p cnf 4 2\n\
             1 2 3 0\n\
             1 4 0\n",
        );
        let mut watcher = Watcher::new(&formula).expect("formula has no empty clauses");
        let mut clauses = formula.clauses.iter_with_clause_indices();
        let (first_clause, _) = clauses.next().unwrap();
        let (second_clause, _) = clauses.next().unwrap();

        let one = Lit::from_int(1);
        let two = Lit::from_int(2);
        let three = Lit::from_int(3);

        assert!(watcher.has_lit(first_clause, &one));
        assert!(watcher.has_lit(first_clause, &two));

        watcher.rewatch(first_clause, &one, &three);

        assert!(!watcher.has_lit(first_clause, &one));
        assert!(watcher.has_lit(first_clause, &three));
        assert!(watcher.has_lit(second_clause, &one));
        assert!(watcher.get_clauses(&one).any(|idx| idx == second_clause));
        assert!(watcher.get_clauses(&three).any(|idx| idx == first_clause));
    }

    #[test]
    fn resolution_removes_the_pivot_and_deduplicates_literals() {
        let a = Clause::from_unique_lits(vec![Lit::from_int(1), Lit::from_int(-2)]);
        let b =
            Clause::from_unique_lits(vec![Lit::from_int(-1), Lit::from_int(3), Lit::from_int(-2)]);

        let resolved = resolve(&a, &b, Lit::from_int(1).var);
        let literals = resolved.iter().copied().collect::<Vec<_>>();

        assert_eq!(literals, vec![Lit::from_int(-2), Lit::from_int(3)]);
    }
}
