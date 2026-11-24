import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth

/-!
# Part I, task `PartI:T08/4/1/1/5` (`TrainStressDivLocal`): reduction to the entries of `Q_c`

Source `the November 2 reference manuscript` lines 326-335 (`Q_c = ∑_{i≠j} V_i ⊗ V_j`
and the error equation), the cross-stress bounds at lines 2217-2234 for `a ≤ c²`.

`div Q_c` has word derivatives that are sums of word derivatives (one letter longer) of the entries
`Q_c^{kl}`. Proved here (`trainStressDivLocal_of`): `TrainStressDivLocal` from the single leaf
`QcJetLocalL2` (local uniform `L²(cell)` bounds of every word derivative of every entry of `Q_c`,
no width condition) together with `qcSmooth_proof` (smoothness of the entries).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf** (lines 326-335, 2217-2234; the entries of `Q_c = ∑_{i≠j} V_i ⊗ V_j` are lattice sums of
Gaussian-times-polynomial profiles, so each word derivative is bounded by `C e^{-γ η²}` locally
uniformly in the width, with no condition `a ≤ c²`): every word derivative of every entry of
`Q_c(r)` lies in `L²(cell)` with squared norm bounded uniformly for `r` near `s > 0`. -/
def QcJetLocalL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ s : ℝ, 0 < s → ∀ (w : List Bool) (k l : Fin 2),
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (B0151.derivWord w (fun x => Qc ν c r x k l)) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (B0151.derivWord w (fun x => Qc ν c r x k l) z) ^ 2 ≤ K

/-- A word derivative of `∂ g` is the word derivative of `g` along the longer word. -/
theorem derivWord_partial_append (b : Bool) (u : List Bool) (g : Plane → ℝ) :
    B0151.derivWord u (B0151.derivWord [b] g) = B0151.derivWord (u ++ [b]) g :=
  (vjl_derivWord_append b g u).symm

/-- Sum of two terms with `L²` bounds. -/
theorem memLp_add_bound {c : ℝ} {A B : Plane → ℝ} {K₁ K₂ : ℝ}
    (hA : MemLp A 2 (Cyl.cellμ c)) (hB : MemLp B 2 (Cyl.cellμ c))
    (h1 : ∫ z in Cyl.cell c, A z ^ 2 ≤ K₁) (h2 : ∫ z in Cyl.cell c, B z ^ 2 ≤ K₂) :
    MemLp (fun z => A z + B z) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (A z + B z) ^ 2 ≤ 2 * (K₁ + K₂) := by
  have hAB : MemLp (A + B) 2 (Cyl.cellμ c) := hA.add hB
  refine ⟨hAB, ?_⟩
  have iA : Integrable (fun z => A z ^ 2) (Cyl.cellμ c) := hA.integrable_sq
  have iB : Integrable (fun z => B z ^ 2) (Cyl.cellμ c) := hB.integrable_sq
  have iAB : Integrable (fun z => (A z + B z) ^ 2) (Cyl.cellμ c) := hAB.integrable_sq
  have hle : ∫ z in Cyl.cell c, (A z + B z) ^ 2 ≤
      ∫ z in Cyl.cell c, (2 * A z ^ 2 + 2 * B z ^ 2) := by
    refine integral_mono iAB ((iA.const_mul 2).add (iB.const_mul 2)) fun z => ?_
    nlinarith [sq_nonneg (A z - B z)]
  refine hle.trans ?_
  have e : ∫ z in Cyl.cell c, (2 * A z ^ 2 + 2 * B z ^ 2) =
      2 * (∫ z in Cyl.cell c, A z ^ 2) + 2 * (∫ z in Cyl.cell c, B z ^ 2) := by
    have := integral_add (μ := Cyl.cellμ c) (iA.const_mul 2) (iB.const_mul 2)
    rw [integral_const_mul, integral_const_mul] at this
    exact this
  rw [e]
  linarith

/-- Component `k` of `div Q` is `∂_q Q^{0k} + ∂_η Q^{1k}`. -/
theorem matDiv_comp (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2) :
    (fun x => Train.matDiv Q x k) = fun x =>
      B0151.derivWord [true] (fun y => Q y 0 k) x + B0151.derivWord [false] (fun y => Q y 1 k) x := by
  funext x
  fin_cases k <;>
    simp only [Train.matDiv, Train.toVec_apply_eq_vcomp, B0146.vcomp] <;> rfl

theorem wordComp_matDiv (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ)
    (hq : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Q z k l)) (w : List Bool) (k : Fin 2) :
    wordComp w (Train.matDiv Q) k = fun z =>
      B0151.derivWord (w ++ [true]) (fun y => Q y 0 k) z +
        B0151.derivWord (w ++ [false]) (fun y => Q y 1 k) z := by
  unfold wordComp
  rw [matDiv_comp]
  rw [ForcingIBP.derivWord_add_smooth w _ _ (B0151.contDiff_derivWord (hq 0 k) [true])
    (B0151.contDiff_derivWord (hq 1 k) [false])]
  funext z
  rw [derivWord_partial_append, derivWord_partial_append]

theorem trainStressDivLocal_of (hQ : QcJetLocalL2) : TrainStressDivLocal := by
  intro ν c hν hc tr htr
  have hc0 : 0 < c := by linarith
  refine ⟨fun r hr => ?_, fun s hs w k => ?_⟩
  · have hq : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Qc ν c r z k l) := fun k l =>
      qcSmooth_proof ν c r hν hc0 hr.le k l
    rw [contDiff_euclidean]
    intro k
    have h := (B0151.contDiff_derivWord (hq 0 k) [true]).add
      (B0151.contDiff_derivWord (hq 1 k) [false])
    have e := matDiv_comp (Qc ν c r) k
    have h2 : ContDiff ℝ ∞ (fun x => Train.matDiv (Qc ν c r) x k) := by
      rw [e]; exact h
    exact h2
  · obtain ⟨e1, he1, K1, h1⟩ := hQ ν c hν hc s hs (w ++ [true]) 0 k
    obtain ⟨e2, he2, K2, h2⟩ := hQ ν c hν hc s hs (w ++ [false]) 1 k
    refine ⟨min e1 e2, lt_min he1 he2, 2 * (K1 + K2), fun r hr hrs => ?_⟩
    have hq : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Qc ν c r z k l) := fun k l =>
      qcSmooth_proof ν c r hν hc0 hr.le k l
    have a1 := h1 r hr (lt_of_lt_of_le hrs (min_le_left _ _))
    have a2 := h2 r hr (lt_of_lt_of_le hrs (min_le_right _ _))
    rw [wordComp_matDiv (Qc ν c r) hq w k]
    exact memLp_add_bound a1.1 a2.1 a1.2 a2.2

end UnforcedLeray.Short.PartI
