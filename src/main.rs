use gcollections::ops::*;
use interval::interval_set::*;
use interval::ops::Range;
use pcp::concept::*;
use pcp::kernel::*;
use pcp::logic::{equivalence, Boolean, Conjunction, NotFormula, Disjunction};
use pcp::propagators::*;
use pcp::search::search_tree_visitor::Status::*;
use pcp::search::*;
use pcp::term::*;
use pcp::variable::ops::*;
use std::collections::HashMap;
use std::ops::Add;

pub type GroupId = usize;
pub type SubjectId = usize;
pub type LecturerId = usize;

pub const HOURS: usize = 20;

#[derive(Debug, Clone)]
struct Problem {
    pub group_requirements: HashMap<GroupId, Vec<(SubjectId, usize)>>, // list of (subject, hours) for each group.
    pub lecturer_requirements: HashMap<LecturerId, usize>,             // hours for each lecturer.
    pub subject_requirements: HashMap<SubjectId, Vec<LecturerId>>, // suitable lecturers for each subject.
}

impl Problem {
    pub fn new(
        group_requirements: HashMap<GroupId, Vec<(SubjectId, usize)>>,
        lecturer_requirements: HashMap<LecturerId, usize>,
        subject_requirements: HashMap<SubjectId, Vec<LecturerId>>,
    ) -> Self {
        Self {
            group_requirements,
            lecturer_requirements,
            subject_requirements,
        }
    }
}

fn solve(problem: Problem) {
    let mut space = FDSpace::empty();
    let mut times: Vec<_> = vec![];
    let mut teachers = vec![];

    for (_group, subjects) in &problem.group_requirements {
        let mut times_for_g = vec![];
        let mut teachers_for_g = vec![];
        for (subject, hours) in subjects {
            for _ in 0..*hours {
                times_for_g.push(Box::new(
                    space.vstore.alloc(IntervalSet::new(0, (HOURS - 1) as i32)),
                ) as Var<VStore>);

                let mut i = IntervalSet::empty();
                for t in problem.subject_requirements.get(subject).unwrap() {
                    i.extend(IntervalSet::new(*t as i32, *t as i32));
                }

                let teacher = Box::new(space.vstore.alloc(i)) as Var<VStore>;
                teachers_for_g.push(teacher);
            }
        }

        times.push(times_for_g);
        teachers.push(teachers_for_g);
    }

    for i in 0..times.len() {
        for (t1, l1) in times[i].iter().zip(teachers[i].iter()) {
            for j in (i + 1)..times.len() {
                for (t2, l2) in times[j].iter().zip(teachers[j].iter()) {
                    space.cstore.alloc(Box::new(
                        Disjunction::new(vec![
                            Box::new(XNeqY::new(t1.bclone(), t2.bclone())),
                            Box::new(XNeqY::new(l1.bclone(), l2.bclone())),
                        ]),
                    ));
                }
            }
        }
    }

    let ls = problem.lecturer_requirements.len();
    for l in 0..ls {
        let const_var = Box::new(
            space.vstore.alloc(IntervalSet::singleton(l as i32)),
        ) as Var<VStore>;
        let const_1 = Box::new(
            space.vstore.alloc(IntervalSet::singleton(1)),
        ) as Var<VStore>;

        let mut vec = Vec::new();
        for i in 0..teachers.len() {
            for v in teachers[i].iter() {
                let temp = Box::new(space.vstore.alloc(IntervalSet::new(0, 1))) as Var<VStore>;
                space.cstore.alloc(Box::new(
                    Disjunction::new(vec![
                        Box::new(
                            Conjunction::new(
                                vec![
                                    Box::new(XEqY::new(v.bclone(), const_var.bclone())),
                                    Box::new(XEqY::new(temp.bclone(), const_1.bclone())),
                                ]
                            ),
                        ),
                        Box::new(
                            Conjunction::new(
                                vec![
                                    Box::new(XNeqY::new(v.bclone(), const_var.bclone())),
                                    Box::new(XNeqY::new(temp.bclone(), const_1.bclone())),
                                ]
                            ),
                        ),
                    ]),
                ));

                vec.push(temp);
            }
        }

        let max = problem.lecturer_requirements.get(&l).copied().unwrap();
        let max = Box::new(space.vstore.alloc(IntervalSet::singleton(max as i32)));
        space.cstore.alloc(Box::new(x_leq_y(Box::new(Sum::new(vec)), max)));
    }

    for times_for_g in times {
        space.cstore.alloc(Box::new(Distinct::new(times_for_g)));
    }

    let mut search = one_solution_engine();
    search.start(&space);
    let (frozen_space, status) = search.enter(space);
    let space = frozen_space.unfreeze();

    // Print result.
    match status {
        Satisfiable => {
            print!("The first solution is:\n[");
            for dom in space.vstore.iter() {
                // At this stage, dom.lower() == dom.upper().
                print!("{}, ", dom.lower());
            }
            println!("]");


            let values = space.vstore.iter().map(|d| d.lower()).collect::<Vec<_>>();

            let mut res1 = vec![];
            let mut res2 = vec![];

            let group_subjects: Vec<_> = problem
                .group_requirements
                .iter()
                .map(|(group, subjects)| {
                    subjects
                        .iter()
                        .map(|(subject, hours)| (0..*hours).map(|_| (*group, *subject)))
                        .flatten()
                })
                .flatten()
                .collect();

            for (i, (group, subject)) in group_subjects.into_iter().enumerate() {
                let hour = values[i * 2] as usize;
                let lecturer = values[i * 2 + 1] as usize;

                res1.push((group, hour, subject, lecturer));
                res2.push((lecturer, hour, subject, group));

                // println!("group {group}, subject {subject}, lecturer {lecturer}, hour {hour}");
            }
            res1.sort();
            res2.sort();

            println!("Schedule ordered by groups");
            for (group, hour, subject, lecturer) in res1 {
                println!("group {group}, hour {hour}, subject {subject}, lecturer {lecturer}");
            }

            println!("\n\n\nSchedule ordered by lecturers");
            for (lecturer, hour, subject, group) in res2 {
                println!("lecturer {lecturer}, hour {hour}, subject {subject}, group {group}");
            }
        }
        Unsatisfiable => println!("Problem is unsatisfiable."),
        EndOfSearch => println!("Search terminated or was interrupted."),
        Unknown(_) => unreachable!(
            "After the search step, the problem instance should be either satisfiable or unsatisfiable.")
    }
}

fn main() {
    let problem = {
        let group_requirements = vec![
            (0_usize, vec![(0_usize, 2_usize), (1, 5), (2, 2), (3, 1)]), // 10
            (1_usize, vec![(0_usize, 1_usize), (3, 2), (4, 6), (2, 1)]), // 10
            (2_usize, vec![(0_usize, 1_usize), (2, 8), (3, 1)]),         // 10
        ]
        .into_iter()
        .collect();
        let lecturer_requirements = vec![(0_usize, 6_usize), (1, 6), (2, 10), (3, 4), (4, 4)]
            .into_iter()
            .collect();
        let subject_requirements = vec![
            (0_usize, vec![3_usize]),
            (1, vec![0, 2]),
            (2, vec![0, 1]),
            (3, vec![4]),
            (4, vec![1, 2]),
        ]
        .into_iter()
        .collect();
        Problem::new(
            group_requirements,
            lecturer_requirements,
            subject_requirements,
        )
    };

    solve(problem);
}
