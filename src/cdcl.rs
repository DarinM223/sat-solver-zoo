use rand::seq::IteratorRandom;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(usize);

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit {
    pub var: Var,
    pub neg: bool,
}

impl Lit {
    pub fn from_int(i: i32) -> Self {
        Lit {
            var: Var(i.unsigned_abs() as usize),
            neg: i.is_negative(),
        }
    }

    pub fn neg(&self) -> Self {
        Lit {
            var: self.var,
            neg: !self.neg,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.var.0 == 0
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.neg {
            write!(f, "¬{}", self.var)
        } else {
            write!(f, "{}", self.var)
        }
    }
}

pub enum ClauseStatus {
    Satisfied,
    Unsatisfied,
    Unit,
    Unresolved,
}

#[derive(Debug, Clone, Default)]
pub struct Clause {
    lits: HashSet<Lit>,
}

impl Clause {
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    pub fn status(&self, assignments: &Assignments) -> ClauseStatus {
        let (count_false, any_true) = self.lits.iter().map(|lit| assignments.value(*lit)).fold(
            (0, false),
            |(count_false, any_true), v| match v {
                Some(true) => (count_false, true),
                Some(false) => (count_false + 1, any_true),
                None => (count_false, any_true),
            },
        );
        if any_true {
            ClauseStatus::Satisfied
        } else if count_false == self.lits.len() {
            ClauseStatus::Unsatisfied
        } else if count_false == self.lits.len() - 1 {
            ClauseStatus::Unit
        } else {
            ClauseStatus::Unresolved
        }
    }
}

impl Hash for Clause {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for lit in self.lits.iter() {
            lit.hash(state);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClauseIndex(usize);

#[derive(Debug, Default)]
pub struct Clauses(Vec<Clause>);

impl Clauses {
    pub fn pop(&mut self) -> Option<Clause> {
        self.0.pop()
    }

    pub fn push(&mut self, clause: Clause) {
        self.0.push(clause);
    }

    pub fn last(&self) -> Option<&Clause> {
        self.0.last()
    }

    pub fn last_mut(&mut self) -> Option<&mut Clause> {
        self.0.last_mut()
    }

    pub fn get(&self, ClauseIndex(i): ClauseIndex) -> Option<&Clause> {
        self.0.get(i)
    }

    pub fn get_mut(&mut self, ClauseIndex(i): ClauseIndex) -> Option<&mut Clause> {
        self.0.get_mut(i)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Clause> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Clause> {
        self.0.iter_mut()
    }
}

impl Index<ClauseIndex> for Clauses {
    type Output = Clause;

    fn index(&self, index: ClauseIndex) -> &Self::Output {
        &self.0[index.0]
    }
}

impl IndexMut<ClauseIndex> for Clauses {
    fn index_mut(&mut self, index: ClauseIndex) -> &mut Self::Output {
        &mut self.0[index.0]
    }
}

pub struct Watcher {
    lit_to_clauses: HashMap<Lit, Vec<ClauseIndex>>,
    clause_to_lits: HashMap<ClauseIndex, Vec<Lit>>,
}

impl Watcher {
    pub fn new(formula: &Formula) -> Self {
        let mut lit_to_clauses: HashMap<Lit, Vec<ClauseIndex>> = HashMap::new();
        let mut clause_to_lits: HashMap<ClauseIndex, Vec<Lit>> = HashMap::new();
        for (clause_idx, clause) in formula.iter_with_clause_indices() {
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

#[derive(Default)]
pub struct Formula {
    clauses: Clauses,
    vars: HashSet<Var>,
}

impl Formula {
    pub fn iter_with_clause_indices(&self) -> impl Iterator<Item = (ClauseIndex, &Clause)> {
        self.clauses
            .iter()
            .enumerate()
            .map(|(i, e)| (ClauseIndex(i), e))
    }

    pub fn new(clauses: Clauses) -> Self {
        let mut vars = HashSet::new();
        for clause in clauses.iter() {
            for lit in clause.lits.iter() {
                vars.insert(lit.var);
            }
        }
        Self { clauses, vars }
    }

    pub fn from_dimacs_cnf(content: &str) -> Self {
        let mut clauses = Clauses::default();
        clauses.push(Clause::default());
        for line in content.lines() {
            let mut tokens = line.split_ascii_whitespace().peekable();
            // Ignore empty lines or lines starting with 'p' or 'c'.
            if let None | Some(&"p" | &"c") = tokens.peek() {
                continue;
            }
            for token in tokens {
                let token = token.parse::<i32>().expect("Expected integer literal");
                let lit = Lit::from_int(token);
                if lit.is_zero() {
                    clauses.push(Clause::default()); // 0 ends a clause in DIMACS CNF.
                } else if let Some(ref mut last) = clauses.last_mut() {
                    last.lits.insert(lit);
                }
            }
        }
        if let Some(clause) = clauses.last()
            && clause.len() == 0
        {
            clauses.pop();
        }
        Self::new(clauses)
    }

    pub fn vars(&self) -> impl Iterator<Item = &Var> {
        self.vars.iter()
    }

    pub fn all_variables_assigned(&self, assignments: &Assignments) -> bool {
        self.vars.len() == assignments.num_assigned_vars()
    }

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

pub struct Assignments {
    len: usize,
    curr_decision_level: u32,
    values: Vec<Option<bool>>,
    antecedents: Vec<Option<ClauseIndex>>,
    decision_levels: Vec<Option<u32>>,
}

impl Assignments {
    pub fn new(size: usize) -> Self {
        Self {
            len: 0,
            curr_decision_level: 0,
            values: vec![None; size],
            antecedents: vec![None; size],
            decision_levels: vec![None; size],
        }
    }

    pub fn num_assigned_vars(&self) -> usize {
        self.len
    }

    pub fn contains_var(&self, var: Var) -> bool {
        self.values[var.0].is_some()
    }

    pub fn value(&self, lit: Lit) -> Option<bool> {
        if lit.neg {
            self.values[lit.var.0].map(std::ops::Not::not)
        } else {
            self.values[lit.var.0]
        }
    }

    pub fn value_var(&self, var: Var) -> Option<bool> {
        self.values[var.0]
    }

    pub fn assign(&mut self, Var(var): Var, value: bool, antecedent: Option<ClauseIndex>) {
        if self.values[var].is_none() {
            self.len += 1;
        }
        self.values[var] = Some(value);
        self.antecedents[var] = antecedent;
        self.decision_levels[var] = Some(self.curr_decision_level);
    }

    pub fn decision_level(&self, Var(var): Var) -> Option<u32> {
        self.decision_levels[var]
    }

    pub fn antecedent(&self, Var(var): Var) -> Option<ClauseIndex> {
        self.antecedents[var]
    }

    pub fn unassign(&mut self, Var(var): Var) {
        if self.values[var].is_some() {
            self.len -= 1;
        }
        self.values[var] = None;
        self.antecedents[var] = None;
        self.decision_levels[var] = None;
    }

    pub fn satisfy(&self, formula: &Formula) -> bool {
        formula
            .clauses
            .iter()
            .all(|clause| clause.lits.iter().any(|lit| self.value(*lit) == Some(true)))
    }

    pub fn backtrack(&mut self, level: u32) {
        for i in 0..self.decision_levels.len() {
            if let Some(decision_level) = self.decision_levels[i]
                && decision_level > level
            {
                self.unassign(Var(i));
            }
        }
    }
}

pub fn add_learnt_clause(
    watcher: &mut Watcher,
    formula: &mut Formula,
    clause: Clause,
    assignments: &Assignments,
) -> ClauseIndex {
    let mut lits = clause.lits.iter().cloned().collect::<Vec<_>>();
    formula.clauses.0.push(clause);

    // add recently assigned literals to watcher
    lits.sort_by(|lit1, lit2| {
        let v1 = assignments.decision_level(lit1.var);
        let v2 = assignments.decision_level(lit2.var);
        v1.cmp(&v2).reverse()
    });
    let clause_idx = ClauseIndex(formula.clauses.0.len() - 1);
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
    let size = formula
        .vars()
        .max()
        .map_or_else(|| formula.vars.len() + 1, |v| v.0 + 1);
    let mut assignments = Assignments::new(size);

    for (clause_idx, clause) in formula
        .iter_with_clause_indices()
        .filter(|(_, clause)| clause.len() == 1)
    {
        let lit = clause.lits.iter().next().unwrap();
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
                .lits
                .iter()
                .filter(|lit| !assignments.contains_var(lit.var))
                .next()
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
            for lit in formula.clauses.get(watching_clause).unwrap().lits.iter() {
                if watcher.has_lit(watching_clause, lit) {
                    continue;
                } else if assignments.value(*lit) == Some(false) {
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
        .lits
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
