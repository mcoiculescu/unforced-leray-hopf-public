import UnforcedLeray.Short.PartIIa.Calc.JetClass.SmoothClosure
import UnforcedLeray.Short.PartIIa.Calc.JetClass.LateEqOps
import UnforcedLeray.Short.PartIIa.Calc.JetClass.LinearOps
import UnforcedLeray.Short.PartIIa.Calc.JetClass.LeibnizMul
import UnforcedLeray.Short.PartIIa.Calc.JetClass.IterCalcComm
import UnforcedLeray.Short.PartIIa.Calc.JetClass.IterCalcLin
import UnforcedLeray.Short.PartIIa.Calc.JetClass.WAlgMisc
import UnforcedLeray.Short.PartIIa.Calc.JetClass.WAlgMul
import UnforcedLeray.Short.PartIIa.Calc.JetClass.WAbsorb
import UnforcedLeray.Short.PartIIa.Calc.JetClass.JLin
import UnforcedLeray.Short.PartIIa.Calc.JetClass.JEMul
import UnforcedLeray.Short.PartIIa.Calc.JetClass.JQMul
import UnforcedLeray.Short.PartIIa.Calc.JetClass.WordShiftE
import UnforcedLeray.Short.PartIIa.Calc.JetClass.WordShiftW

/-!
# Part II-a, the jet toolkit (task `PartII-a:R02/8/15`, Lean name `jetToolkit`)

Assembly of the fourteen leaf proofs of `JetClass.lean` into the single bundle `JetToolkit`.
No new mathematics: the classes `JCongr`, `JLin`, `JEMul`, `JQMul` and `JEToJQ` are
assembled into `JetCalculus`, and the word reductions are supplied by `wordShiftE_of` and
`wordShiftW_of`.

Source of record: `the November 2 reference manuscript`, lines 1243-1285.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.Jet

/-- The jet toolkit: every calculus statement of `JetClass.lean` (one theorem, shared by the
blocks `PartII-a:R02/8-12`). -/
theorem jetToolkit : JetToolkit := by
  have hJLin : JLin := jLin_of smoothClosure lateEqOps linearOps wAlgMisc
  have hJEMul : JEMul := jeMul_of smoothClosure lateEqOps leibnizMul wAlgMul wAbsorb hJLin
  have hJQMul : JQMul := jqMul_of smoothClosure lateEqOps leibnizMul wAlgMul hJLin hJEMul
  have hJc : JetCalculus :=
    { hcongr := jCongr_of lateEqOps
      hlin := hJLin
      hemul := hJEMul
      hqmul := hJQMul
      hofE := jeToJQ_of wAbsorb }
  exact
    { smooth := smoothClosure
      eqOps := lateEqOps
      linOps := linearOps
      leib := leibnizMul
      comm := iterCalcComm
      iterLin := iterCalcLin
      wmisc := wAlgMisc
      wmul := wAlgMul
      wabs := wAbsorb
      jc := hJc
      wordE := wordShiftE_of smoothClosure iterCalcComm iterCalcLin
      wordW := wordShiftW_of smoothClosure iterCalcComm iterCalcLin }

end UnforcedLeray.Short.PartIIa.Jet
