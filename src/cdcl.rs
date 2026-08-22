use rand::seq::IteratorRandom;
use std::{
    collections::HashSet,
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

#[derive(Clone, Copy)]
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

#[derive(Default)]
pub struct Formula {
    clauses: Clauses,
    vars: HashSet<Var>,
}

impl Formula {
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

    pub fn add_learnt_clause(&mut self, clause: Clause) {
        self.clauses.0.push(clause);
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

pub fn cdcl_solve(formula: &mut Formula) -> Option<Assignments> {
    let size = formula
        .vars()
        .max()
        .map_or_else(|| formula.vars.len() + 1, |v| v.0 + 1);
    let mut assignments = Assignments::new(size);
    match unit_propagation(formula, &mut assignments) {
        Reason::Conflict(_) => return None,
        Reason::Unresolved => {}
    };

    while !formula.all_variables_assigned(&assignments) {
        let (var, val) = formula.pick_branching_variable(&assignments);
        assignments.curr_decision_level += 1;
        assignments.assign(var, val, None);
        loop {
            let clause = match unit_propagation(formula, &mut assignments) {
                Reason::Conflict(clause_index) => clause_index,
                Reason::Unresolved => break,
            };

            let (backtrack_level, clause) =
                conflict_analysis(formula, formula.clauses.get(clause).unwrap(), &assignments)?;
            formula.add_learnt_clause(clause);
            assignments.backtrack(backtrack_level);
            assignments.curr_decision_level = backtrack_level;
        }
    }

    Some(assignments)
}

pub enum Reason {
    Conflict(ClauseIndex),
    Unresolved,
}

pub fn unit_propagation(formula: &Formula, assignments: &mut Assignments) -> Reason {
    // finish is set to true when no unit and conflict clause is found.
    let mut finish = false;
    while !finish {
        finish = true;
        for (clause_idx, clause) in formula.clauses.iter().enumerate() {
            let clause_idx = ClauseIndex(clause_idx);
            match clause.status(assignments) {
                ClauseStatus::Unresolved | ClauseStatus::Satisfied => continue,
                ClauseStatus::Unit => {
                    let lit = clause
                        .lits
                        .iter()
                        .find(|lit| assignments.values[lit.var.0].is_none())
                        .unwrap();
                    assignments.assign(lit.var, !lit.neg, Some(clause_idx));
                    finish = false;
                }
                ClauseStatus::Unsatisfied => return Reason::Conflict(clause_idx),
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
