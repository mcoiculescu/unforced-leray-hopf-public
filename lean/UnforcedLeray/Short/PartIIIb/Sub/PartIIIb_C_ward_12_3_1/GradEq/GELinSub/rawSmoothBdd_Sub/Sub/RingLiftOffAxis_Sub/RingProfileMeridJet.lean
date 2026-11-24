import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RingProfileJet

/-!
# Organizer `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/5`: `ringProfileMeridJet`

Source of record: `the November 2 reference manuscript`
(SP), lines 1207-1212 (the meridional vector `b = (-Psi_eta, Psi_q + R^{-1}(Psi - 2 s Psi_s - eta Psi_eta))`).

The vector `ringStreamProfile R Phi` is the combination `b0 • m0 + b1 • m1` of the two components,
each of which is smooth on `s > 0` with the bounds of `IIb.ringProfileJet`; the Euclidean norm of
the combination is controlled by the components, since `m0`, `m1` are unit vectors.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray

/-- Every meridional vector is the combination of its two components in the basis `m0, m1`. -/
theorem merid_eq_comb (v : Axi.Merid) : v = v 0 • Axi.m0 + v 1 • Axi.m1 := by
  ext i
  fin_cases i <;> simp [Axi.m0, Axi.m1]

theorem norm_m0_eq_one : ‖Axi.m0‖ = 1 := by
  simp [Axi.m0]

theorem norm_m1_eq_one : ‖Axi.m1‖ = 1 := by
  simp [Axi.m1]

/-- Derivatives of `z ↦ b z • m` on the open set `s > 0`: `‖D^n (b • m)‖ ≤ ‖m‖ ‖D^n b‖`. -/
theorem norm_iteratedFDeriv_smul_const_le {b : ℝ × (ℝ × ℝ) → ℝ} {m : Axi.Merid}
    {y : ℝ × (ℝ × ℝ)} (hmem : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (hb : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => b z • m) y‖ ≤ ‖m‖ * ‖iteratedFDeriv ℝ n b y‖ := by
  set L : ℝ →L[ℝ] Axi.Merid := (ContinuousLinearMap.id ℝ ℝ).smulRight m with hLdef
  have hL : ‖L‖ ≤ ‖m‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m) fun t => by
    simp [hLdef, norm_smul, mul_comm]
  have hfun : (fun z => b z • m) = L ∘ b := by
    funext z
    simp [hLdef]
  have hc : ContDiffAt ℝ n b y := UnforcedLeray.Short.IIb.contDiffAt_of_mem hb hmem
  rw [hfun]
  exact (L.norm_iteratedFDeriv_comp_left hc le_rfl).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- The Euclidean norm of the `i`-th derivative of a two-component combination. -/
theorem norm_iteratedFDeriv_comb_le {b0 b1 : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)}
    (hy : 0 < y.1)
    (h0 : ContDiffOn ℝ ∞ b0 (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (h1 : ContDiffOn ℝ ∞ b1 (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z => b0 z • Axi.m0 + b1 z • Axi.m1) y‖ ≤
      ‖iteratedFDeriv ℝ i b0 y‖ + ‖iteratedFDeriv ℝ i b1 y‖ := by
  have hmem : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := UnforcedLeray.Short.IIb.mem_Uo.2 hy
  have hc0 : ContDiffAt ℝ i b0 y := UnforcedLeray.Short.IIb.contDiffAt_of_mem h0 hmem
  have hc1 : ContDiffAt ℝ i b1 y := UnforcedLeray.Short.IIb.contDiffAt_of_mem h1 hmem
  have hs0 : ContDiffAt ℝ i (fun z => b0 z • Axi.m0) y := hc0.smul_const _
  have hs1 : ContDiffAt ℝ i (fun z => b1 z • Axi.m1) y := hc1.smul_const _
  have hadd : iteratedFDeriv ℝ i (fun z => b0 z • Axi.m0 + b1 z • Axi.m1) y =
      iteratedFDeriv ℝ i (fun z => b0 z • Axi.m0) y +
        iteratedFDeriv ℝ i (fun z => b1 z • Axi.m1) y :=
    iteratedFDeriv_add_apply hs0 hs1
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have e0 := norm_iteratedFDeriv_smul_const_le hmem h0 (m := Axi.m0) i
  have e1 := norm_iteratedFDeriv_smul_const_le hmem h1 (m := Axi.m1) i
  rw [norm_m0_eq_one, one_mul] at e0
  rw [norm_m1_eq_one, one_mul] at e1
  linarith

theorem contDiffOn_comb {b0 b1 : ℝ × (ℝ × ℝ) → ℝ}
    (h0 : ContDiffOn ℝ ∞ b0 (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (h1 : ContDiffOn ℝ ∞ b1 (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) :
    ContDiffOn ℝ ∞ (fun z => b0 z • Axi.m0 + b1 z • Axi.m1)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  (h0.smul_const Axi.m0).add (h1.smul_const Axi.m1)

/-- **Jets of the ring stream profile as a meridional vector** (SP 1207-1212): the vector
`ringStreamProfile R Φ` is `C^∞` on `s > 0`, and its derivatives are bounded by the Leibniz
bounds of `IIb.ringProfileJet`. -/
theorem ringProfileMeridJet : UnforcedLeray.Short.PartIIIb.Concrete.RingProfileMeridJet := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.RingProfileMeridJet
  intro R Φ hΦ
  obtain ⟨h0, h1, hb⟩ := UnforcedLeray.Short.IIb.ringProfileJet R Φ hΦ
  have hfun : Axi.ringStreamProfile R Φ =
      fun z => Axi.ringStreamProfile R Φ z 0 • Axi.m0 + Axi.ringStreamProfile R Φ z 1 • Axi.m1 :=
    funext fun z => merid_eq_comb _
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact contDiffOn_comb (b0 := fun z => Axi.ringStreamProfile R Φ z 0)
      (b1 := fun z => Axi.ringStreamProfile R Φ z 1) h0 h1
  · intro i
    obtain ⟨C, hC⟩ := hb i
    refine ⟨2 * |C|, fun y hy => ?_⟩
    obtain ⟨hA, hB⟩ := hC y hy
    have hcomb := norm_iteratedFDeriv_comb_le (b0 := fun z => Axi.ringStreamProfile R Φ z 0)
      (b1 := fun z => Axi.ringStreamProfile R Φ z 1) (y := y) hy h0 h1 i
    have hS : 0 ≤ ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hW : 1 ≤ 1 + |y.1| + |y.2.2| := by
      have := abs_nonneg y.1
      have := abs_nonneg y.2.2
      linarith
    have hW0 : 0 ≤ 1 + |y.1| + |y.2.2| := by linarith
    have hCW : C ≤ |C| * (1 + |y.1| + |y.2.2|) :=
      (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hW)
    have h1' : C * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ ≤
        |C| * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
      mul_le_mul_of_nonneg_right hCW hS
    have h2' : C * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ ≤
        |C| * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C) hW0) hS
    have hsplit : 2 * |C| * (1 + |y.1| + |y.2.2|) *
        ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ =
        |C| * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ +
        |C| * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := by
      ring
    rw [hfun]
    refine hcomb.trans ?_
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete
