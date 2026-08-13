use std::{
    collections::{BTreeSet, HashSet},
    fmt::Display,
    ops::{Index, IndexMut},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(usize);

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit {
    pub var: Var,
    pub neg: bool,
}

impl Lit {
    fn from_int(i: i32) -> Self {
        Lit {
            var: Var(i.unsigned_abs() as usize),
            neg: i.is_negative(),
        }
    }

    fn neg(&self) -> Self {
        Lit {
            var: self.var,
            neg: !self.neg,
        }
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

#[derive(Clone)]
pub struct Clause {
    lits: HashSet<Lit>,
}

impl Clause {
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

pub struct Clauses(Vec<Clause>);

impl Clauses {
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

pub struct Formula {
    clauses: Clauses,
    vars: HashSet<Var>,
}

#[derive(Default)]
pub struct Assignments {
    curr_decision_level: u32,
    values: Vec<Option<bool>>,
    antecedents: Vec<Option<ClauseIndex>>,
    decision_levels: Vec<Option<u32>>,
}

impl Assignments {
    pub fn value(&self, lit: Lit) -> Option<bool> {
        if lit.neg {
            self.values[lit.var.0].map(std::ops::Not::not)
        } else {
            self.values[lit.var.0]
        }
    }

    pub fn assign(&mut self, Var(var): Var, value: bool, antecedent: Option<ClauseIndex>) {
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
        self.values[var] = None;
        self.antecedents[var] = None;
        self.decision_levels[var] = None;
    }

    pub fn satisfy(&self, formula: Formula) -> bool {
        formula
            .clauses
            .iter()
            .all(|clause| clause.lits.iter().any(|lit| self.value(*lit) == Some(true)))
    }
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

    let decision_levels = clause
        .lits
        .iter()
        .flat_map(|lit| assignments.decision_level(lit.var))
        .collect::<BTreeSet<_>>();
    if decision_levels.len() <= 1 {
        Some((0, clause))
    } else {
        unimplemented!()
    }
}
