import UnforcedLeray.Short.PartIIa.Calc.JetClass

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

/-- **Sizes add under products** (`JQMul`, nonnegative sizes). -/
theorem jqMul_of (h1 : SmoothClosure) (h2 : LateEqOps) (h4 : LeibnizMul) (h8 : WAlgMul)
    (hL : JLin) (hE : JEMul) : JQMul := by
  have hC := jCongr_of h2
  have qm : ∀ (n : ℕ) (a a' : ℝ) (F G : Fam), 0 ≤ a → 0 ≤ a' → JQ n a F → JQ n a' G →
      JQ n (a + a') (F * G) := by
    intro n
    induction n with
    | zero =>
      intro a a' F G ha ha' hF hG
      exact ⟨(h1 F G (JQ.smooth hF) (JQ.smooth hG)).2.1, h8.1 a a' F G (JQ.ww hF) (JQ.ww hG)⟩
    | succ n ih =>
      intro a a' F G ha ha' hF hG
      have hsF := JQ.smooth hF
      have hsG := JQ.smooth hG
      have hLb := h4 F G hsF hsG
      have hG0 : JQ n 0 G := hL.2.2.2.1 n a' 0 G ha' (JQ.down hG)
      have hF0 : JQ n 0 F := hL.2.2.2.1 n a 0 F ha (JQ.down hF)
      have hK1 := ih a a' (famK F) G ha ha' (JQ.k hF) (JQ.down hG)
      have hK2 := ih a a' F (famK G) ha ha' (JQ.down hF) (JQ.k hG)
      have hEt1 := ih (a + 1 / 2) a' (famEta F) G (by linarith) ha' (JQ.eta hF) (JQ.down hG)
      have hEt2 := ih a (a' + 1 / 2) F (famEta G) ha (by linarith) (JQ.down hF) (JQ.eta hG)
      have hQ1 := (hE.2 n G (famQ F) hG0 (JQ.q hF)).2
      have hQ2 := (hE.2 n F (famQ G) hF0 (JQ.q hG)).1
      exact ⟨(h1 F G hsF hsG).2.1, h8.1 a a' F G (JQ.ww hF) (JQ.ww hG),
        hC.1 n (a + a') _ _ hLb.1.symm (hL.1 n (a + a') _ _ hK1 hK2),
        hC.1 n (a + a' + 1 / 2) _ _ hLb.2.1.symm
          (hL.1 n (a + a' + 1 / 2) _ _ (JQ.cast (show a + 1 / 2 + a' = a + a' + 1 / 2 by ring) hEt1)
            (JQ.cast (show a + (a' + 1 / 2) = a + a' + 1 / 2 by ring) hEt2)),
        hC.2 n _ _ hLb.2.2.symm (hL.2.2.2.2.1 n _ _ hQ1 hQ2)⟩
  exact fun n a a' F G ha ha' hF hG => qm n a a' F G ha ha' hF hG

end UnforcedLeray.Short.PartIIa.Jet
