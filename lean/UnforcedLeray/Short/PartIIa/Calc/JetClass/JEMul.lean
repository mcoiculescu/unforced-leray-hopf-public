import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

/-- **Exponentially small times bounded is exponentially small** (`JEMul`). -/
theorem jeMul_of (h1 : SmoothClosure) (h2 : LateEqOps) (h4 : LeibnizMul) (h8 : WAlgMul)
    (h9 : WAbsorb) (hL : JLin) : JEMul := by
  have hC := jCongr_of h2
  have hE1 : ∀ (n : ℕ) (F G : Fam), JE n F → JE n G → JE n (F * G) := by
    intro n
    induction n with
    | zero =>
      intro F G hF hG
      exact ⟨(h1 F G (JE.smooth hF) (JE.smooth hG)).2.1,
        (h8.2 F G (h9 0 F (JE.we hF)) (JE.we hG)).1⟩
    | succ n ih =>
      intro F G hF hG
      have hsF := JE.smooth hF
      have hsG := JE.smooth hG
      have hLb := h4 F G hsF hsG
      exact ⟨(h1 F G hsF hsG).2.1, (h8.2 F G (h9 0 F (JE.we hF)) (JE.we hG)).1,
        hC.2 n _ _ hLb.1.symm (hL.2.2.2.2.1 n _ _
          (ih _ _ (JE.k hF) (JE.down hG)) (ih _ _ (JE.down hF) (JE.k hG))),
        hC.2 n _ _ hLb.2.1.symm (hL.2.2.2.2.1 n _ _
          (ih _ _ (JE.eta hF) (JE.down hG)) (ih _ _ (JE.down hF) (JE.eta hG))),
        hC.2 n _ _ hLb.2.2.symm (hL.2.2.2.2.1 n _ _
          (ih _ _ (JE.q hF) (JE.down hG)) (ih _ _ (JE.down hF) (JE.q hG)))⟩
  have hE2 : ∀ (n : ℕ) (F G : Fam), JQ n 0 F → JE n G → JE n (F * G) ∧ JE n (G * F) := by
    intro n
    induction n with
    | zero =>
      intro F G hF hG
      have hW := h8.2 F G (JQ.ww hF) (JE.we hG)
      exact ⟨⟨(h1 F G (JQ.smooth hF) (JE.smooth hG)).2.1, hW.1⟩,
        ⟨(h1 G F (JE.smooth hG) (JQ.smooth hF)).2.1, hW.2⟩⟩
    | succ n ih =>
      intro F G hF hG
      have hsF := JQ.smooth hF
      have hsG := JE.smooth hG
      have hLb := h4 F G hsF hsG
      have hLbG := h4 G F hsG hsF
      have hF0 : JQ n 0 (famEta F) :=
        hL.2.2.2.1 n (0 + 1 / 2) 0 (famEta F) (by norm_num) (JQ.eta hF)
      have P1 := ih (famK F) G (JQ.k hF) (JE.down hG)
      have P2 := ih F (famK G) (JQ.down hF) (JE.k hG)
      have P3 := ih (famEta F) G hF0 (JE.down hG)
      have P4 := ih F (famEta G) (JQ.down hF) (JE.eta hG)
      have P5 := hE1 n (famQ F) G (JQ.q hF) (JE.down hG)
      have P6 := hE1 n G (famQ F) (JE.down hG) (JQ.q hF)
      have P7 := ih F (famQ G) (JQ.down hF) (JE.q hG)
      have hW := h8.2 F G (JQ.ww hF) (JE.we hG)
      exact ⟨⟨(h1 F G hsF hsG).2.1, hW.1,
          hC.2 n _ _ hLb.1.symm (hL.2.2.2.2.1 n _ _ P1.1 P2.1),
          hC.2 n _ _ hLb.2.1.symm (hL.2.2.2.2.1 n _ _ P3.1 P4.1),
          hC.2 n _ _ hLb.2.2.symm (hL.2.2.2.2.1 n _ _ P5 P7.1)⟩,
        ⟨(h1 G F hsG hsF).2.1, hW.2,
          hC.2 n _ _ hLbG.1.symm (hL.2.2.2.2.1 n _ _ P2.2 P1.2),
          hC.2 n _ _ hLbG.2.1.symm (hL.2.2.2.2.1 n _ _ P4.2 P3.2),
          hC.2 n _ _ hLbG.2.2.symm (hL.2.2.2.2.1 n _ _ P7.2 P6)⟩⟩
  exact ⟨fun n F G hF hG => hE1 n F G hF hG, fun n F G hF hG => hE2 n F G hF hG⟩

end UnforcedLeray.Short.PartIIa.Jet
