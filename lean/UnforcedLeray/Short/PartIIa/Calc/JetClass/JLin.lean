import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

/-- **Linear closure** of the jet classes, size monotonicity, and `0 ∈ JE` (`JLin`). -/
theorem jLin_of (h1 : SmoothClosure) (h2 : LateEqOps) (h3 : LinearOps) (h7 : WAlgMisc) : JLin := by
  have hC := jCongr_of h2
  have eAdd : ∀ (n : ℕ) (F G : Fam), JE n F → JE n G → JE n (F + G) := by
    intro n
    induction n with
    | zero =>
      intro F G hF hG
      exact ⟨(h1 F G (JE.smooth hF) (JE.smooth hG)).1, (JE.we hF).add (JE.we hG)⟩
    | succ n ih =>
      intro F G hF hG
      have hsF := JE.smooth hF
      have hsG := JE.smooth hG
      obtain ⟨hK, hEta, hQ, -, -, -, -, -, -, -, -, -⟩ := h3 F G hsF hsG 0
      exact ⟨(h1 F G hsF hsG).1, (JE.we hF).add (JE.we hG),
        hC.2 n _ _ hK.symm (ih _ _ (JE.k hF) (JE.k hG)),
        hC.2 n _ _ hEta.symm (ih _ _ (JE.eta hF) (JE.eta hG)),
        hC.2 n _ _ hQ.symm (ih _ _ (JE.q hF) (JE.q hG))⟩
  have eSmul : ∀ (n : ℕ) (F : Fam) (k : ℝ), JE n F → JE n (k • F) := by
    intro n
    induction n with
    | zero =>
      intro F k hF
      exact ⟨(h1 F F (JE.smooth hF) (JE.smooth hF)).2.2.1 k, WE.smul k (JE.we hF)⟩
    | succ n ih =>
      intro F k hF
      have hsF := JE.smooth hF
      obtain ⟨-, -, -, hK, hEta, hQ, -, -, -, -, -, -⟩ := h3 F F hsF hsF k
      exact ⟨(h1 F F hsF hsF).2.2.1 k, WE.smul k (JE.we hF),
        hC.2 n _ _ hK.symm (ih _ k (JE.k hF)),
        hC.2 n _ _ hEta.symm (ih _ k (JE.eta hF)),
        hC.2 n _ _ hQ.symm (ih _ k (JE.q hF))⟩
  have eNu : ∀ (n : ℕ) (F : Fam), JE n F → JE n (famNu F) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact ⟨(h1 F F (JE.smooth hF) (JE.smooth hF)).2.2.2.1, h7.2.2 F (JE.we hF)⟩
    | succ n ih =>
      intro F hF
      have hsF := JE.smooth hF
      obtain ⟨-, -, -, -, -, -, hK, hEta, hQ, -, -, -⟩ := h3 F F hsF hsF 0
      exact ⟨(h1 F F hsF hsF).2.2.2.1, h7.2.2 F (JE.we hF),
        hC.2 n _ _ hK.symm (ih _ (JE.k hF)),
        hC.2 n _ _ hEta.symm (ih _ (JE.eta hF)),
        hC.2 n _ _ hQ.symm (ih _ (JE.q hF))⟩
  have eZero : ∀ n : ℕ, JE n (0 : Fam) := by
    intro n
    induction n with
    | zero => exact ⟨JSmooth.zero, WE.zero⟩
    | succ n ih =>
      obtain ⟨-, -, -, -, -, -, -, -, -, hK, hEta, hQ⟩ := h3 0 0 JSmooth.zero JSmooth.zero 0
      exact ⟨JSmooth.zero, WE.zero,
        hC.2 n _ _ hK.symm ih, hC.2 n _ _ hEta.symm ih, hC.2 n _ _ hQ.symm ih⟩
  have qMono : ∀ (n : ℕ) (a a' : ℝ) (F : Fam), a' ≤ a → JQ n a F → JQ n a' F := by
    intro n
    induction n with
    | zero =>
      intro a a' F hle hF
      exact ⟨JQ.smooth hF, h7.1 a a' F hle (JQ.ww hF)⟩
    | succ n ih =>
      intro a a' F hle hF
      exact ⟨JQ.smooth hF, h7.1 a a' F hle (JQ.ww hF), ih a a' _ hle (JQ.k hF),
        ih (a + 1 / 2) (a' + 1 / 2) _ (by linarith) (JQ.eta hF), JQ.q hF⟩
  have qAdd : ∀ (n : ℕ) (a : ℝ) (F G : Fam), JQ n a F → JQ n a G → JQ n a (F + G) := by
    intro n
    induction n with
    | zero =>
      intro a F G hF hG
      exact ⟨(h1 F G (JQ.smooth hF) (JQ.smooth hG)).1, WW.add (JQ.ww hF) (JQ.ww hG)⟩
    | succ n ih =>
      intro a F G hF hG
      have hsF := JQ.smooth hF
      have hsG := JQ.smooth hG
      obtain ⟨hK, hEta, hQ, -, -, -, -, -, -, -, -, -⟩ := h3 F G hsF hsG 0
      exact ⟨(h1 F G hsF hsG).1, WW.add (JQ.ww hF) (JQ.ww hG),
        hC.1 n a _ _ hK.symm (ih a _ _ (JQ.k hF) (JQ.k hG)),
        hC.1 n (a + 1 / 2) _ _ hEta.symm (ih (a + 1 / 2) _ _ (JQ.eta hF) (JQ.eta hG)),
        hC.2 n _ _ hQ.symm (eAdd n _ _ (JQ.q hF) (JQ.q hG))⟩
  have qSmul : ∀ (n : ℕ) (a : ℝ) (F : Fam) (k : ℝ), JQ n a F → JQ n a (k • F) := by
    intro n
    induction n with
    | zero =>
      intro a F k hF
      exact ⟨(h1 F F (JQ.smooth hF) (JQ.smooth hF)).2.2.1 k, WW.smul k (JQ.ww hF)⟩
    | succ n ih =>
      intro a F k hF
      have hsF := JQ.smooth hF
      obtain ⟨-, -, -, hK, hEta, hQ, -, -, -, -, -, -⟩ := h3 F F hsF hsF k
      exact ⟨(h1 F F hsF hsF).2.2.1 k, WW.smul k (JQ.ww hF),
        hC.1 n a _ _ hK.symm (ih a _ k (JQ.k hF)),
        hC.1 n (a + 1 / 2) _ _ hEta.symm (ih (a + 1 / 2) _ k (JQ.eta hF)),
        hC.2 n _ _ hQ.symm (eSmul n _ k (JQ.q hF))⟩
  have qNu : ∀ (n : ℕ) (a : ℝ) (F : Fam), JQ n a F → JQ n a (famNu F) := by
    intro n
    induction n with
    | zero =>
      intro a F hF
      exact ⟨(h1 F F (JQ.smooth hF) (JQ.smooth hF)).2.2.2.1, h7.2.1 a F (JQ.ww hF)⟩
    | succ n ih =>
      intro a F hF
      have hsF := JQ.smooth hF
      obtain ⟨-, -, -, -, -, -, hK, hEta, hQ, -, -, -⟩ := h3 F F hsF hsF 0
      exact ⟨(h1 F F hsF hsF).2.2.2.1, h7.2.1 a F (JQ.ww hF),
        hC.1 n a _ _ hK.symm (ih a _ (JQ.k hF)),
        hC.1 n (a + 1 / 2) _ _ hEta.symm (ih (a + 1 / 2) _ (JQ.eta hF)),
        hC.2 n _ _ hQ.symm (eNu n _ (JQ.q hF))⟩
  exact ⟨fun n a F G hF hG => qAdd n a F G hF hG,
    fun n a F k hF => qSmul n a F k hF,
    fun n a F hF => qNu n a F hF,
    fun n a a' F hle hF => qMono n a a' F hle hF,
    fun n F G hF hG => eAdd n F G hF hG,
    fun n F k hF => eSmul n F k hF,
    fun n F hF => eNu n F hF,
    fun n => eZero n⟩

end UnforcedLeray.Short.PartIIa.Jet
