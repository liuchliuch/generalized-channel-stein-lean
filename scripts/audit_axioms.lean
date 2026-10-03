import Paper.Proofs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Transitive axiom audit

Audit every theorem and safe definition declared in the imported project
and vendored modules, including private declarations and declarations outside the project
namespace. The module inventory comes from Lean's compiled environment.
-/
open Lean Elab Command

set_option maxHeartbeats 0

run_elab do
  let env ← getEnv
  let mut roots : Array Name := #[]
  let mut modules := 0
  let mut theorems := 0
  let mut definitions := 0
  for i in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    unless (`GeneralizedChannelStein).isPrefixOf moduleName ||
        (`QuantumChannelStein).isPrefixOf moduleName ||
        (`Quantum).isPrefixOf moduleName || (`QuantumInfo).isPrefixOf moduleName ||
        (`Physlib).isPrefixOf moduleName ||
        (#[`SingletonTheory, `SingletonSteinBridge, `TupleCoherence, `TupleStates,
          `OrdinaryStateStein, `KernelFilledAlternative, `StateSteinDirect]).contains moduleName ||
        moduleName == `Paper.Statements || moduleName == `Paper.Proofs do
      continue
    modules := modules + 1
    let data := env.header.moduleData[i]!
    for j in [:data.constNames.size] do
      let name := data.constNames[j]!
      match data.constants[j]! with
      | .thmInfo _ =>
        roots := roots.push name
        theorems := theorems + 1
      | .defnInfo info =>
        unless info.safety == .safe do
          -- Compiler-generated runtime implementations are not mathematical roots.
          continue
        roots := roots.push name
        definitions := definitions + 1
      | .axiomInfo _ => throwError "Project axiom declaration: {name}"
      | _ => pure ()
  unless modules > 0 && theorems > 0 && definitions > 0 do
    throwError "Empty or incomplete project declaration inventory"
  let (_, result) := ((roots.forM CollectAxioms.collect).run env).run {}
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in result.axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected transitive axiom: {axiomName}"
  logInfo m!"Audited {modules} modules: {theorems} theorems and {definitions} definitions."
  logInfo m!"Permitted axiom union: {result.axioms}"
