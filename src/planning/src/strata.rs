use crate::arithmetic::{ArithmeticArgument, FactorArgument};
use crate::collections::{Collection, CollectionSignature};
use crate::compare::ComparisonExprArgument;
use crate::constraints::BaseConstraints;
use crate::flow::TransformationFlow;
use crate::rule::RuleQueryPlan;
use catalog::atoms::AtomArgumentSignature;
use catalog::rule::Catalog;
use parsing::rule::FLRule;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use crate::arguments::TransformationArgument;
use crate::transformations::Transformation;

/* a group of non-recursive strata or a recursive stratum */
#[derive(Debug, Clone)]
pub struct GroupStrataQueryPlan {
    is_recursive: bool,
    rules: Vec<FLRule>,

    enter_scope: HashSet<Arc<CollectionSignature>>,                                                    // base and intermediates rel to bring into scope
    last_signatures_map: HashMap<Arc<CollectionSignature>, Vec<Arc<CollectionSignature>>>,             // sinks of the dataflow DAG (map head to a vector of last signatures)

    reverse_last_signatures_map: HashMap<Arc<CollectionSignature>, Vec<Arc<CollectionSignature>>>,      // reverse map for the last signatures
    strata_plan: Vec<Vec<Transformation>>,
    per_rule_last_collection: Vec<Arc<Collection>>,                                                    // output collection of the root transformation per rule (for shared plans)

}

impl GroupStrataQueryPlan {
    pub fn new(
        is_recursive: bool,
        rule_plans: Vec<RuleQueryPlan>,
        seen_set: &mut HashSet<Arc<CollectionSignature>>,
        disable_sharing: bool,
    ) -> Self {
        let rules = rule_plans
            .iter()
            .map(|rp| rp.rule().clone())
            .collect::<Vec<FLRule>>();

        // populate the last_signatures_map (map head to a vector of last signatures)
        let last_signatures_map = rule_plans.iter().fold(
            HashMap::new(),
            |mut map: HashMap<Arc<CollectionSignature>, Vec<Arc<CollectionSignature>>>, rp| {
                let head = Arc::new(CollectionSignature::new_atom(rp.rule().head().name()));
                map.entry(head)
                    .or_default()
                    .push(Arc::clone(rp.rule_plan().0.output().signature()));
                map
            },
        );

        // populate the reverse_last_signatures_map (map last signature to a its heads)
        let mut reverse_last_signatures_map: HashMap<Arc<CollectionSignature>, Vec<Arc<CollectionSignature>>> = HashMap::new();
        for (head_signature, last_signatures) in last_signatures_map.iter() {
            for last_signature in last_signatures {
                reverse_last_signatures_map
                    .entry(Arc::clone(last_signature))
                    .or_default()
                    .push(Arc::clone(head_signature));
            }
        }

        // store the output collection of the root transformation per rule (before plan construction)
        let per_rule_last_collection = rule_plans.iter()
            .map(|rp| Arc::clone(rp.rule_plan().0.output()))
            .collect::<Vec<Arc<Collection>>>();

        /* init */
        let mut strata_plan = Vec::new();
        let mut enter_scope = HashSet::new();
        let mut nested_seen = HashSet::new();

        for rule_plan in rule_plans.iter() {
            let (root, transformation_tree) = rule_plan.rule_plan();

            if !is_recursive {
                strata_plan.push(Self::construct_non_recursive(
                    seen_set,
                    root,
                    &transformation_tree,
                    disable_sharing,
                ));
            } else {
                let (rule_plan, rule_enter_scope) = Self::construct_recursive(
                    seen_set,
                    &mut nested_seen,
                    root,
                    &transformation_tree,
                    disable_sharing,
                );
                strata_plan.push(rule_plan);
                enter_scope.extend(rule_enter_scope);
            }
        }

        Self {
            is_recursive,
            rules,
            enter_scope,
            last_signatures_map,
            reverse_last_signatures_map,
            strata_plan,
            per_rule_last_collection
        }
    }

    fn construct_non_recursive(
        seen: &mut HashSet<Arc<CollectionSignature>>,
        root: &Transformation,
        transformation_tree: &HashMap<Transformation, (Transformation, Transformation)>,
        disable_sharing: bool,
    ) -> Vec<Transformation> {
        let output_signature = root.output().signature();

        // base case (already seen) - skip if sharing is disabled
        if !disable_sharing && seen.contains(output_signature) {
            return vec![];
        }

        // mark as seen only if sharing is enabled
        if !disable_sharing {
            seen.insert(Arc::clone(output_signature));
        }

        transformation_tree.get(root).map_or_else(
            || vec![root.clone()], // leaf op
            |(l_root, r_root)| {
                // recursive case
                let mut plan = Vec::new();
                plan.extend(Self::construct_non_recursive(
                    seen,
                    l_root,
                    transformation_tree,
                    disable_sharing,
                ));
                plan.extend(Self::construct_non_recursive(
                    seen,
                    r_root,
                    transformation_tree,
                    disable_sharing,
                ));
                plan.push(root.clone());
                plan
            },
        )
    }

    fn construct_recursive(
        seen: &mut HashSet<Arc<CollectionSignature>>,
        nested_seen: &mut HashSet<Arc<CollectionSignature>>,
        root: &Transformation,
        transformation_tree: &HashMap<Transformation, (Transformation, Transformation)>,
        disable_sharing: bool,
    ) -> (Vec<Transformation>, HashSet<Arc<CollectionSignature>>) {
        let output_signature = root.output().signature();

        // base case (already seen) - skip if sharing is disabled
        if !disable_sharing && seen.contains(output_signature) {
            // it can't be the that global scope has an intermediate rel that is produced by some recursive idb of this strata (we can safely reuse it)
            // debug!("borrow {} from global", output_signature);
            return (vec![], HashSet::from([Arc::clone(&output_signature)]));
        }

        // base case (already nested_seen) - skip if sharing is disabled
        if !disable_sharing && nested_seen.contains(output_signature) {
            // debug!("borrow {} from nested", output_signature);
            return (vec![], HashSet::new());
        }

        // mark as nested_seen only if sharing is enabled
        if !disable_sharing {
            nested_seen.insert(Arc::clone(output_signature));
        }

        transformation_tree.get(root).map_or_else(
            // base case (enter base atom into scope at a leaf op)
            // (careful) enter_scope contains idbs that are first defined in the recursive strata, the execution layer should inspect those and fetch from variables_map
            || {
                (
                    vec![root.clone()],
                    HashSet::from([Arc::clone(root.unary().signature())]),
                )
            },
            |(l_root, r_root)| {
                // recursive case
                let (l_plan, l_enter_scope) = Self::construct_recursive(
                    seen,
                    nested_seen,
                    l_root,
                    transformation_tree,
                    disable_sharing,
                );
                let (r_plan, r_enter_scope) = Self::construct_recursive(
                    seen,
                    nested_seen,
                    r_root,
                    transformation_tree,
                    disable_sharing,
                );

                (
                    l_plan
                        .into_iter()
                        .chain(r_plan)
                        .chain(std::iter::once(root.clone()))
                        .collect(),
                    l_enter_scope.union(&r_enter_scope).cloned().collect(),
                )
            },
        )
    }

    pub fn is_recursive(&self) -> bool {
        self.is_recursive
    }

    pub fn rules(&self) -> &Vec<FLRule> {
        &self.rules
    }

    pub fn strata_plan(&self) -> Vec<&Transformation> {
        self.strata_plan.iter().flatten().collect()
    }

    // head collection signatures of the strata
    pub fn head_signatures_set(&self) -> HashSet<Arc<CollectionSignature>> {
        self.last_signatures_map
            .keys()
            // (sideways) jump over sip rules
            .filter(|signature| !signature.name().contains("_sip"))
            .cloned()
            .collect()
    }

    // heads (name and arity) of the strata
    pub fn heads(&self) -> HashMap<String, usize> {
        self.rules
            .iter()
            .map(|rule| (rule.head().name().to_string(), rule.head().arity()))
            .collect()
    }

    pub fn last_signatures_map(
        &self,
    ) -> &HashMap<Arc<CollectionSignature>, Vec<Arc<CollectionSignature>>> {
        &self.last_signatures_map
    }

    pub fn reverse_last_signatures_map(&self) -> &HashMap<Arc<CollectionSignature>, Vec<Arc<CollectionSignature>>> {
        &self.reverse_last_signatures_map
    }

    pub fn enter_scope_set(&self) -> &HashSet<Arc<CollectionSignature>> {
        &self.enter_scope
    }
}

impl fmt::Display for GroupStrataQueryPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.enter_scope.is_empty() {
            // print the first one
            write!(f, "[ent] {}", self.enter_scope.iter().next().unwrap())?;
            // print the rest
            for signature in self.enter_scope.iter().skip(1) {
                write!(f, " && {}", signature)?;
            }
            write!(f, "\n")?;
        }

        // if strata_plan is empty, print noop
        if self.strata_plan.is_empty() {
            write!(f, "[∅]")
        } else {
            write!(
                f,
                "{}",
                self.strata_plan
                    .iter()
                    .enumerate()
                    .map(|(i, transformations_per_rule)| {
                        let print_per_rule = transformations_per_rule
                            .iter()
                            .enumerate()
                            .map(|(j, transformation)| {
                                let prefix = if j == transformations_per_rule.len() - 1 {
                                    "└── "
                                } else {
                                    "├── "
                                };
                                format!("  {}{}", prefix, transformation)
                            })
                            .collect::<Vec<String>>()
                            .join("\n");

                        format!("{}\n{}", &self.rules[i], print_per_rule)
                    })
                    .collect::<Vec<String>>()
                    .join("\n")
            )
        }
    }
}

// ── helpers for to_datalog_rules ──────────────────────────────────────────────

fn sig_to_var(sig: &AtomArgumentSignature, catalog: &Catalog) -> String {
    catalog
        .signature_to_argument_str_map()
        .get(sig)
        .cloned()
        .unwrap_or_else(|| "_".to_string())
}

fn type_prefix(sig: &CollectionSignature) -> &'static str {
    match sig {
        CollectionSignature::UnaryTransformationOutput { name } => {
            if name.starts_with("Kv") { "kv" }
            else if name.starts_with('K') { "k_" }
            else { "rw" }
        }
        CollectionSignature::JnOutput { .. }    => "jn",
        CollectionSignature::NegJnOutput { .. } => "nj",
        CollectionSignature::Atom { .. } => unreachable!(),
    }
}

fn lookup_dl_name(
    sig: &Arc<CollectionSignature>,
    name_map: &HashMap<Arc<CollectionSignature>, String>,
) -> String {
    if sig.is_atom() {
        sig.name().to_string()
    } else {
        name_map[sig].clone()
    }
}

fn collection_dl_args(coll: &Collection, catalog: &Catalog) -> Vec<String> {
    coll.key_argument_signatures()
        .iter()
        .chain(coll.value_argument_signatures().iter())
        .map(|sig| sig_to_var(sig, catalog))
        .collect()
}

fn format_atom(
    coll: &Collection,
    catalog: &Catalog,
    negate: bool,
    name_map: &HashMap<Arc<CollectionSignature>, String>,
) -> String {
    let name = lookup_dl_name(coll.signature(), name_map);
    let args = collection_dl_args(coll, catalog).join(", ");
    if negate { format!("!{}({})", name, args) } else { format!("{}({})", name, args) }
}

fn resolve_kv_arg(
    ta: &TransformationArgument,
    keys: &[AtomArgumentSignature],
    vals: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    match ta {
        TransformationArgument::KV((is_value, id)) => {
            if *is_value {
                sig_to_var(&vals[*id], catalog)
            } else {
                sig_to_var(&keys[*id], catalog)
            }
        }
        _ => panic!("resolve_kv_arg: expected KV argument, got {:?}", ta),
    }
}

fn resolve_jn_arg(
    ta: &TransformationArgument,
    lk: &[AtomArgumentSignature],
    lv: &[AtomArgumentSignature],
    rv: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    match ta {
        TransformationArgument::Jn((is_right, is_value, id)) => {
            if !is_right {
                if *is_value {
                    sig_to_var(&lv[*id], catalog)
                } else {
                    sig_to_var(&lk[*id], catalog)
                }
            } else {
                // right side: only values; join key comes from left
                sig_to_var(&rv[*id], catalog)
            }
        }
        _ => panic!("resolve_jn_arg: expected Jn argument, got {:?}", ta),
    }
}

fn format_factor_kv(
    fa: &FactorArgument,
    keys: &[AtomArgumentSignature],
    vals: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    match fa {
        FactorArgument::Var(ta) => resolve_kv_arg(ta, keys, vals, catalog),
        FactorArgument::Const(c) => format!("{}", c),
    }
}

fn format_arithmetic_kv(
    aa: &ArithmeticArgument,
    keys: &[AtomArgumentSignature],
    vals: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    let mut s = format_factor_kv(aa.init(), keys, vals, catalog);
    for (op, factor) in aa.rest() {
        s.push_str(&format!(" {} {}", op, format_factor_kv(factor, keys, vals, catalog)));
    }
    s
}

fn format_compare_kv(
    ca: &ComparisonExprArgument,
    keys: &[AtomArgumentSignature],
    vals: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    format!(
        "{} {} {}",
        format_arithmetic_kv(ca.left(), keys, vals, catalog),
        ca.operator(),
        format_arithmetic_kv(ca.right(), keys, vals, catalog)
    )
}

fn format_factor_jn(
    fa: &FactorArgument,
    lk: &[AtomArgumentSignature],
    lv: &[AtomArgumentSignature],
    rv: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    match fa {
        FactorArgument::Var(ta) => resolve_jn_arg(ta, lk, lv, rv, catalog),
        FactorArgument::Const(c) => format!("{}", c),
    }
}

fn format_arithmetic_jn(
    aa: &ArithmeticArgument,
    lk: &[AtomArgumentSignature],
    lv: &[AtomArgumentSignature],
    rv: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    let mut s = format_factor_jn(aa.init(), lk, lv, rv, catalog);
    for (op, factor) in aa.rest() {
        s.push_str(&format!(" {} {}", op, format_factor_jn(factor, lk, lv, rv, catalog)));
    }
    s
}

fn format_compare_jn(
    ca: &ComparisonExprArgument,
    lk: &[AtomArgumentSignature],
    lv: &[AtomArgumentSignature],
    rv: &[AtomArgumentSignature],
    catalog: &Catalog,
) -> String {
    format!(
        "{} {} {}",
        format_arithmetic_jn(ca.left(), lk, lv, rv, catalog),
        ca.operator(),
        format_arithmetic_jn(ca.right(), lk, lv, rv, catalog)
    )
}

fn kv_guards(
    flow: &TransformationFlow,
    input: &Collection,
    catalog: &Catalog,
) -> Vec<String> {
    let (keys, vals) = input.kv_argument_signatures();
    let constraints: &BaseConstraints = flow.constraints();
    let mut guards = Vec::new();

    for (ta, constant) in constraints.constant_eq_constraints().iter() {
        let var = resolve_kv_arg(ta, keys, vals, catalog);
        guards.push(format!("{} = {}", var, constant));
    }
    for (ta1, ta2) in constraints.variable_eq_constraints().iter() {
        let var1 = resolve_kv_arg(ta1, keys, vals, catalog);
        let var2 = resolve_kv_arg(ta2, keys, vals, catalog);
        guards.push(format!("{} = {}", var1, var2));
    }
    for ca in flow.compares() {
        guards.push(format_compare_kv(ca, keys, vals, catalog));
    }
    guards
}

fn jn_guards(
    flow: &TransformationFlow,
    left: &Collection,
    right: &Collection,
    catalog: &Catalog,
) -> Vec<String> {
    let (lk, lv) = left.kv_argument_signatures();
    let (_, rv) = right.kv_argument_signatures();
    flow.compares()
        .iter()
        .map(|ca| format_compare_jn(ca, lk, lv, rv, catalog))
        .collect()
}

impl GroupStrataQueryPlan {
    /// Renders each transformation in the plan as a Datalog rule.
    ///
    /// The catalog is rebuilt per rule from the stored `FLRule` so the caller does
    /// not need to pass one explicitly.  Intermediate relations are named after the
    /// sanitised `CollectionSignature::debug_name()`; the last transformation for
    /// each rule uses the real head predicate name.
    /// First pass: assign a short sequential name to every unique intermediate
    /// CollectionSignature that appears anywhere in this group's plan.
    /// Atom signatures (EDB/IDB base relations) are not entered into the map —
    /// they keep their own name.
    /// Registers the OUTPUT signature of every transformation in this group into
    /// `name_map`, using the next available `counter` value.  Input signatures are
    /// intentionally skipped: they were either atoms (no entry needed) or already
    /// registered as outputs by an earlier group, and we must not assign them a
    /// second counter name.
    pub fn populate_name_map(
        &self,
        name_map: &mut HashMap<Arc<CollectionSignature>, String>,
        counter: &mut usize,
    ) {
        for sig in self
            .strata_plan
            .iter()
            .flatten()
            .map(|t| Arc::clone(t.output().signature()))
            .chain(self.per_rule_last_collection.iter().map(|c| Arc::clone(c.signature())))
        {
            if sig.is_atom() || name_map.contains_key(&sig) {
                continue;
            }
            name_map.insert(Arc::clone(&sig), format!("{}{}", type_prefix(&sig), *counter));
            *counter += 1;
        }
    }

    /// Returns (dl_name, total_arity) for every relation this group defines —
    /// both intermediate collections and the final head predicates.
    /// EDB atom relations are excluded (they are declared separately by the input file).
    pub fn collect_declarations(
        &self,
        name_map: &HashMap<Arc<CollectionSignature>, String>,
    ) -> Vec<(String, usize)> {
        let mut seen: HashSet<String> = HashSet::new();
        let mut result = Vec::new();

        // intermediate outputs
        for t in self.strata_plan.iter().flatten() {
            let sig = t.output().signature();
            if sig.is_atom() { continue; }
            let dl_name = lookup_dl_name(sig, name_map);
            if seen.insert(dl_name.clone()) {
                let (k, v) = t.output().arity();
                result.push((dl_name, k + v));
            }
        }

        // head predicates
        for (rule_idx, transformations) in self.strata_plan.iter().enumerate() {
            let head_name = self.rules[rule_idx].head().name().to_string();
            if seen.insert(head_name.clone()) {
                let arity = if transformations.is_empty() {
                    let (k, v) = self.per_rule_last_collection[rule_idx].arity();
                    k + v
                } else {
                    let last = transformations.last().unwrap();
                    let (k, v) = last.output().arity();
                    k + v
                };
                result.push((head_name, arity));
            }
        }

        result
    }

    pub fn to_datalog_rules(&self, name_map: &HashMap<Arc<CollectionSignature>, String>) -> Vec<String> {
        let mut rules = Vec::new();

        for (rule_idx, transformations) in self.strata_plan.iter().enumerate() {
            let rule = &self.rules[rule_idx];
            let catalog = Catalog::from_strata(rule);
            let head_name = rule.head().name();

            if transformations.is_empty() {
                // Shared computation: the root transformation was already emitted for a prior rule.
                // Emit a single projection rule from the shared intermediate to this head.
                let last_coll = &self.per_rule_last_collection[rule_idx];
                let last_name = lookup_dl_name(last_coll.signature(), &name_map);
                let args = collection_dl_args(last_coll, &catalog).join(", ");
                rules.push(format!("{}({}) :- {}({}).", head_name, args, last_name, args));
                continue;
            }

            let len = transformations.len();
            for (t_idx, t) in transformations.iter().enumerate() {
                let is_last = t_idx == len - 1;
                let out_name = if is_last {
                    head_name.to_string()
                } else {
                    lookup_dl_name(t.output().signature(), &name_map)
                };
                let out_args = collection_dl_args(t.output(), &catalog).join(", ");

                let (body_atoms, guards): (Vec<String>, Vec<String>) = match t {
                    Transformation::RowToRow { input, flow, .. }
                    | Transformation::RowToK { input, flow, .. }
                    | Transformation::RowToKv { input, flow, .. }
                    | Transformation::KvToKv { input, flow, .. }
                    | Transformation::KvToK { input, flow, .. } => {
                        let body = vec![format_atom(input, &catalog, false, &name_map)];
                        let guards = kv_guards(flow, input, &catalog);
                        (body, guards)
                    }
                    Transformation::JnKK { input, flow, .. }
                    | Transformation::JnKKv { input, flow, .. }
                    | Transformation::JnKvK { input, flow, .. }
                    | Transformation::JnKvKv { input, flow, .. }
                    | Transformation::Cartesian { input, flow, .. } => {
                        let (left, right) = input;
                        let body = vec![
                            format_atom(left, &catalog, false, &name_map),
                            format_atom(right, &catalog, false, &name_map),
                        ];
                        let guards = jn_guards(flow, left, right, &catalog);
                        (body, guards)
                    }
                    Transformation::NjKvK { input, .. }
                    | Transformation::NjKK { input, .. } => {
                        let (left, right) = input;
                        let body = vec![
                            format_atom(left, &catalog, false, &name_map),
                            format_atom(right, &catalog, true, &name_map),
                        ];
                        (body, vec![])
                    }
                };

                let body_str = body_atoms
                    .into_iter()
                    .chain(guards)
                    .collect::<Vec<_>>()
                    .join(", ");

                rules.push(format!("{}({}) :- {}.", out_name, out_args, body_str));
            }
        }

        rules
    }
}
