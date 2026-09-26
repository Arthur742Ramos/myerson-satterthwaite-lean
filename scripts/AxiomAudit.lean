import Solution

open Lean

run_cmd do
  let env ← getEnv
  let comparatorDefinitions : List Name := [
    `interimQ, `interimR, `interimU, `interimW
  ]
  let names := (env.constants.toList.map Prod.fst).filter fun name =>
    name.toString.startsWith "MS." || comparatorDefinitions.contains name
  let names := names.toArray.qsort Name.lt
  for name in names do
    let axioms ← Lean.collectAxioms name
    let body := String.intercalate ", " (axioms.toList.map Name.toString)
    logInfo m!"'{name}' depends on axioms: [{body}]"
  logInfo m!"PALOMAR-AXIOM-AUDIT-COVERAGE: {names.size} declarations"
