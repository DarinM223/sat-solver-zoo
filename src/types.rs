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
    pub lits: HashSet<Lit>,
}

impl Clause {
    pub fn iter(&self) -> impl Iterator<Item = &Lit> + Clone {
        self.lits.iter()
    }

    pub fn len(&self) -> usize {
        self.lits.len()
    }

    pub fn add_lit(&mut self, lit: Lit) {
        self.lits.insert(lit);
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

    pub fn push(&mut self, clause: Clause) -> ClauseIndex {
        self.0.push(clause);
        ClauseIndex(self.0.len() - 1)
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

    pub fn iter_with_clause_indices(&self) -> impl Iterator<Item = (ClauseIndex, &Clause)> {
        self.0.iter().enumerate().map(|(i, e)| (ClauseIndex(i), e))
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

pub struct Assignments {
    pub curr_decision_level: u32,
    len: usize,
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

#[derive(Default)]
pub struct Formula {
    pub clauses: Clauses,
    pub vars: HashSet<Var>,
}

impl Formula {
    pub fn new(clauses: Clauses) -> Self {
        let mut vars = HashSet::new();
        for clause in clauses.iter() {
            for lit in clause.iter() {
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
                    last.add_lit(lit);
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

    pub fn max_var_size(&self) -> usize {
        self.vars()
            .max()
            .map_or_else(|| self.vars.len() + 1, |v| v.0 + 1)
    }
}
