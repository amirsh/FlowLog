use crate::arithmetic::{ArithmeticArgument, FactorArgument};
use crate::collections::{Collection, CollectionSignature};
use crate::compare::ComparisonExprArgument;
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


// ── flow-inversion helpers (fix for cross-group catalog mismatch) ─────────────
//
// When an input collection was produced by a *prior* GroupStrataQueryPlan, its
// AtomArgumentSignature values belong to that prior group's catalog and cannot
// be resolved via the current group's catalog (sig_to_var → "_").  Instead we
// *invert* the TransformationFlow: output argument signatures ARE from the
// current catalog, so we derive each input-position variable name by finding
// which output position it maps to and using that output variable name.

/// Derives (in_key_vars, in_val_vars) for the input of a KVToKV transformation.
fn derive_kv_input_vars(
    input: &Collection,
    output: &Collection,
    flow: &TransformationFlow,
    catalog: &Catalog,
) -> (Vec<String>, Vec<String>) {
    let out_keys: Vec<String> = output.key_argument_signatures().iter()
        .map(|s| sig_to_var(s, catalog)).collect();
    let out_vals: Vec<String> = output.value_argument_signatures().iter()
        .map(|s| sig_to_var(s, catalog)).collect();

    let (in_key_arity, in_val_arity) = input.arity();
    let mut in_key_vars = vec!["_".to_string(); in_key_arity];
    let mut in_val_vars = vec!["_".to_string(); in_val_arity];

    match flow {
        TransformationFlow::KVToKV { key, value, .. } => {
            for (i, ta) in key.iter().enumerate() {
                if let TransformationArgument::KV((is_val, id)) = ta {
                    let var = out_keys[i].clone();
                    if *is_val { in_val_vars[*id] = var; } else { in_key_vars[*id] = var; }
                }
            }
            for (i, ta) in value.iter().enumerate() {
                if let TransformationArgument::KV((is_val, id)) = ta {
                    let var = out_vals[i].clone();
                    if *is_val { in_val_vars[*id] = var; } else { in_key_vars[*id] = var; }
                }
            }
        }
        _ => panic!("derive_kv_input_vars: expected KVToKV flow"),
    }

    (in_key_vars, in_val_vars)
}

/// Derives ((lk_vars, lv_vars), rv_vars) for the inputs of a JnToKV transformation.
fn derive_jn_input_vars(
    left: &Collection,
    right: &Collection,
    output: &Collection,
    flow: &TransformationFlow,
    catalog: &Catalog,
) -> ((Vec<String>, Vec<String>), Vec<String>) {
    let out_keys: Vec<String> = output.key_argument_signatures().iter()
        .map(|s| sig_to_var(s, catalog)).collect();
    let out_vals: Vec<String> = output.value_argument_signatures().iter()
        .map(|s| sig_to_var(s, catalog)).collect();

    let (lk_arity, lv_arity) = left.arity();
    let (_, rv_arity) = right.arity();
    let mut lk_vars = vec!["_".to_string(); lk_arity];
    let mut lv_vars = vec!["_".to_string(); lv_arity];
    let mut rv_vars = vec!["_".to_string(); rv_arity];

    match flow {
        TransformationFlow::JnToKV { key, value, .. } => {
            for (i, ta) in key.iter().enumerate() {
                if let TransformationArgument::Jn((is_right, is_val, id)) = ta {
                    let var = out_keys[i].clone();
                    if !is_right {
                        if *is_val { lv_vars[*id] = var; } else { lk_vars[*id] = var; }
                    } else {
                        rv_vars[*id] = var;
                    }
                }
            }
            for (i, ta) in value.iter().enumerate() {
                if let TransformationArgument::Jn((is_right, is_val, id)) = ta {
                    let var = out_vals[i].clone();
                    if !is_right {
                        if *is_val { lv_vars[*id] = var; } else { lk_vars[*id] = var; }
                    } else {
                        rv_vars[*id] = var;
                    }
                }
            }
        }
        _ => panic!("derive_jn_input_vars: expected JnToKV flow"),
    }

    ((lk_vars, lv_vars), rv_vars)
}

fn format_atom_with_vars(name: &str, vars: &[String], negate: bool) -> String {
    let args = vars.join(", ");
    if negate { format!("!{}({})", name, args) } else { format!("{}({})", name, args) }
}

fn resolve_kv_arg_vars(ta: &TransformationArgument, key_vars: &[String], val_vars: &[String]) -> String {
    match ta {
        TransformationArgument::KV((is_val, id)) => {
            if *is_val { val_vars[*id].clone() } else { key_vars[*id].clone() }
        }
        _ => panic!("resolve_kv_arg_vars: expected KV argument"),
    }
}

fn resolve_jn_arg_vars(ta: &TransformationArgument, lk: &[String], lv: &[String], rv: &[String]) -> String {
    match ta {
        TransformationArgument::Jn((is_right, is_val, id)) => {
            if !is_right {
                if *is_val { lv[*id].clone() } else { lk[*id].clone() }
            } else {
                rv[*id].clone()
            }
        }
        _ => panic!("resolve_jn_arg_vars: expected Jn argument"),
    }
}

fn format_factor_kv_vars(fa: &FactorArgument, key_vars: &[String], val_vars: &[String]) -> String {
    match fa {
        FactorArgument::Var(ta) => resolve_kv_arg_vars(ta, key_vars, val_vars),
        FactorArgument::Const(c) => format!("{}", c),
    }
}

fn format_arithmetic_kv_vars(aa: &ArithmeticArgument, key_vars: &[String], val_vars: &[String]) -> String {
    let mut s = format_factor_kv_vars(aa.init(), key_vars, val_vars);
    for (op, factor) in aa.rest() {
        s.push_str(&format!(" {} {}", op, format_factor_kv_vars(factor, key_vars, val_vars)));
    }
    s
}

fn format_compare_kv_vars(ca: &ComparisonExprArgument, key_vars: &[String], val_vars: &[String]) -> String {
    format!(
        "{} {} {}",
        format_arithmetic_kv_vars(ca.left(), key_vars, val_vars),
        ca.operator(),
        format_arithmetic_kv_vars(ca.right(), key_vars, val_vars),
    )
}

fn format_factor_jn_vars(fa: &FactorArgument, lk: &[String], lv: &[String], rv: &[String]) -> String {
    match fa {
        FactorArgument::Var(ta) => resolve_jn_arg_vars(ta, lk, lv, rv),
        FactorArgument::Const(c) => format!("{}", c),
    }
}

fn format_arithmetic_jn_vars(aa: &ArithmeticArgument, lk: &[String], lv: &[String], rv: &[String]) -> String {
    let mut s = format_factor_jn_vars(aa.init(), lk, lv, rv);
    for (op, factor) in aa.rest() {
        s.push_str(&format!(" {} {}", op, format_factor_jn_vars(factor, lk, lv, rv)));
    }
    s
}

fn format_compare_jn_vars(ca: &ComparisonExprArgument, lk: &[String], lv: &[String], rv: &[String]) -> String {
    format!(
        "{} {} {}",
        format_arithmetic_jn_vars(ca.left(), lk, lv, rv),
        ca.operator(),
        format_arithmetic_jn_vars(ca.right(), lk, lv, rv),
    )
}

fn kv_guards_with_vars(flow: &TransformationFlow, key_vars: &[String], val_vars: &[String]) -> Vec<String> {
    let constraints = flow.constraints();
    let mut guards = Vec::new();
    for (ta, constant) in constraints.constant_eq_constraints().iter() {
        let var = resolve_kv_arg_vars(ta, key_vars, val_vars);
        guards.push(format!("{} = {}", var, constant));
    }
    for (ta1, ta2) in constraints.variable_eq_constraints().iter() {
        let var1 = resolve_kv_arg_vars(ta1, key_vars, val_vars);
        let var2 = resolve_kv_arg_vars(ta2, key_vars, val_vars);
        guards.push(format!("{} = {}", var1, var2));
    }
    for ca in flow.compares() {
        guards.push(format_compare_kv_vars(ca, key_vars, val_vars));
    }
    guards
}

fn jn_guards_with_vars(flow: &TransformationFlow, lk: &[String], lv: &[String], rv: &[String]) -> Vec<String> {
    flow.compares()
        .iter()
        .map(|ca| format_compare_jn_vars(ca, lk, lv, rv))
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
                        let (in_key_vars, in_val_vars) =
                            derive_kv_input_vars(input, t.output(), flow, &catalog);
                        let in_vars: Vec<String> =
                            in_key_vars.iter().chain(in_val_vars.iter()).cloned().collect();
                        let name = lookup_dl_name(input.signature(), name_map);
                        let body = vec![format_atom_with_vars(&name, &in_vars, false)];
                        let guards = kv_guards_with_vars(flow, &in_key_vars, &in_val_vars);
                        (body, guards)
                    }
                    Transformation::JnKK { input, flow, .. }
                    | Transformation::JnKKv { input, flow, .. }
                    | Transformation::JnKvK { input, flow, .. }
                    | Transformation::JnKvKv { input, flow, .. }
                    | Transformation::Cartesian { input, flow, .. } => {
                        let (left, right) = input;
                        let ((lk_vars, lv_vars), rv_vars) =
                            derive_jn_input_vars(left, right, t.output(), flow, &catalog);
                        let left_vars: Vec<String> =
                            lk_vars.iter().chain(lv_vars.iter()).cloned().collect();
                        let right_vars: Vec<String> =
                            lk_vars.iter().chain(rv_vars.iter()).cloned().collect();
                        let left_name = lookup_dl_name(left.signature(), name_map);
                        let right_name = lookup_dl_name(right.signature(), name_map);
                        let body = vec![
                            format_atom_with_vars(&left_name, &left_vars, false),
                            format_atom_with_vars(&right_name, &right_vars, false),
                        ];
                        let guards = jn_guards_with_vars(flow, &lk_vars, &lv_vars, &rv_vars);
                        (body, guards)
                    }
                    Transformation::NjKvK { input, flow, .. }
                    | Transformation::NjKK { input, flow, .. } => {
                        let (left, right) = input;
                        let ((lk_vars, lv_vars), _rv_vars) =
                            derive_jn_input_vars(left, right, t.output(), flow, &catalog);
                        let left_vars: Vec<String> =
                            lk_vars.iter().chain(lv_vars.iter()).cloned().collect();
                        let left_name = lookup_dl_name(left.signature(), name_map);
                        let right_name = lookup_dl_name(right.signature(), name_map);
                        // right is key-only (negated); its key = join key = lk_vars
                        let body = vec![
                            format_atom_with_vars(&left_name, &left_vars, false),
                            format_atom_with_vars(&right_name, &lk_vars, true),
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
