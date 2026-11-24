import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.Eq.Integrable
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.Eq.Decomp

/-!
# Leaf `PartII-b:T11/2/2/2` (`DualTestEq`)

Complexification of `FlatEqCellStream` (SP 1923-1927): `FlatEqCellStream` applied to `Re ψ` and
`Im ψ`; `flatTransposeC (perpC ψ) = flatTranspose (∇^⊥ Re ψ) + i flatTranspose (∇^⊥ Im ψ)`
(`Eq/Decomp.lean`), and both pairings are integrable for `ageμ c 0` (`Eq/Integrable.lean`: on the
box `σ ≤ s ≤ H`, `|η| ≤ L` the `H_r` weight is bounded below).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem DualTestEq_proof : UnforcedLeray.Short.IIb.DualTestEq := by
  intro hcs c r ν μ b hc hν hr hb hfl ψ hψ hper hvan
  obtain ⟨σ, Hh, Lm, hσ, hv⟩ := hvan
  set ψr : Coord → ℝ := fun z => (ψ z).re with hψr
  set ψi : Coord → ℝ := fun z => (ψ z).im with hψi
  have hψr_s : ContDiff ℝ ∞ ψr := Complex.reCLM.contDiff.comp hψ
  have hψi_s : ContDiff ℝ ∞ ψi := Complex.imCLM.contDiff.comp hψ
  have hre := hcs c r ν μ b hc hν hr hb hfl ψr hψr_s (fun x => by simp [hψr, hper x])
    ⟨σ, Hh, Lm, hσ, fun x hx => by simp [hψr, hv x hx]⟩
  have him := hcs c r ν μ b hc hν hr hb hfl ψi hψi_s (fun x => by simp [hψi, hper x])
    ⟨σ, Hh, Lm, hσ, fun x hx => by simp [hψi, hv x hx]⟩
  -- the open set where `ψ` vanishes
  set U : Set Coord := {x | x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|} with hU
  have hUo : IsOpen U := by
    refine (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hvr : ∀ y ∈ U, ψr y = 0 := fun y hy => by simp [hψr, hv y hy]
  have hvi : ∀ y ∈ U, ψi y = 0 := fun y hy => by simp [hψi, hv y hy]
  have hbox : ∀ x, x ∉ dtBox σ Hh Lm → x ∈ U := by
    intro x hx
    by_contra hxU
    apply hx
    simp only [hU, mem_setOf_eq, not_or, not_lt] at hxU
    exact ⟨⟨hxU.1, hxU.2.1⟩, trivial, abs_le.1 hxU.2.2⟩
  have hIA := integrable_pair_of_box hc hr hb σ Hh Lm hσ
    (fun x i => flatTranspose ν μ (dtStream ψr) x i)
    (flatTranspose_dtStream_continuous ν μ ψr hψr_s)
    (fun x hx i => flatTranspose_dtStream_zero ν μ U hUo ψr hvr x (hbox x hx) i)
  have hIB := integrable_pair_of_box hc hr hb σ Hh Lm hσ
    (fun x i => flatTranspose ν μ (dtStream ψi) x i)
    (flatTranspose_dtStream_continuous ν μ ψi hψi_s)
    (fun x hx i => flatTranspose_dtStream_zero ν μ U hUo ψi hvi x (hbox x hx) i)
  have hpt : ∀ x, pairC b (fun y => flatTransposeC ν μ (perpC ψ) y) x =
      (∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψr) x i) +
        Complex.I * ∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψi) x i := by
    intro x
    unfold pairC
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [flatTransposeC_perpC_split ν μ ψ hψ x i]
    ring
  simp_rw [hpt]
  rw [integral_add hIA (hIB.const_mul Complex.I), integral_const_mul]
  have h1 : ∫ x, ∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψr) x i ∂(Axi.ageμ c 0) = 0 :=
    hre
  have h2 : ∫ x, ∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψi) x i ∂(Axi.ageμ c 0) = 0 :=
    him
  rw [h1, h2]; simp

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.DualTestEq_proof
