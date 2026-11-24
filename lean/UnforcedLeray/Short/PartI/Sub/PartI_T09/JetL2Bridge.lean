import UnforcedLeray.Short.PartI.Sub.PartI_T09
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.Spine.Proofs.EstEuclidBridge

/-!
# `PartI:T09` leaf 3a: the `L²` jet bridge (`JetL2Bridge`, source lines 355-357)

The operator-norm jet of a `Vec`-valued field is bounded pointwise by the sum of the absolute
values of all coordinate word derivatives (`norm_iteratedFDeriv_euclid2_le` and `cylJetWord_proof`).
Each coordinate word derivative is in `L²(cell)`, its `L²` norm is at most the square root of the
jet energy (`jetEnergy` is a sum of nonnegative integrals), and the index set has at most `2 · 2^j`
elements. This gives `‖D^j f‖_{L²(cell)} ≤ 2 · 2^j · √(jetEnergy)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- The `L²` norm of `|g|` is the square root of `∫ g²`. -/
lemma jl2_abs_eLpNorm (μ : Measure Plane) (g : Plane → ℝ) (hg : MemLp g 2 μ) :
    eLpNorm (fun z => |g z|) 2 μ = ENNReal.ofReal (Real.sqrt (∫ z, g z ^ 2 ∂μ)) := by
  have h := hg.norm.eLpNorm_eq_integral_rpow_norm (two_ne_zero) (by norm_num)
  have e1 : (fun z => |g z|) = fun z => ‖g z‖ := by
    funext z
    rw [Real.norm_eq_abs]
  have e2 : ∀ a, ‖‖g a‖‖ ^ (2 : ℝ) = g a ^ 2 := fun a => by
    rw [norm_norm, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [e1, h]
  simp only [e2, ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow, one_div]

/-- A single word energy is at most the jet energy. -/
lemma jl2_energy_le (c : ℝ) (j : ℕ) (f : Plane → Vec) (hf : CellSmoothL2 c f)
    (w : List Bool) (hw : w ∈ wordsOfLength j) (k : Fin 2) :
    ∫ z, wordComp w f k z ^ 2 ∂(volume.restrict (Cyl.cell c)) ≤ jetEnergy c j f := by
  have hint : ∀ (v : List Bool) (l : Fin 2),
      Integrable (fun z => wordComp v f l z * wordComp v f l z)
        (volume.restrict (Cyl.cell c)) := by
    intro v l
    have h := (hf.2.2 v l).integrable_sq
    simp only [sq] at h ⊢
    exact h
  have hJ : jetEnergy c j f = ∑ v ∈ wordsOfLength j, ∑ l : Fin 2,
      ∫ z, wordComp v f l z * wordComp v f l z ∂(volume.restrict (Cyl.cell c)) := by
    unfold jetEnergy jetPair
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun l _ => hint v l))]
    apply Finset.sum_congr rfl
    intro v _
    rw [integral_finsetSum _ (fun l _ => hint v l)]
  rw [hJ]
  simp only [sq]
  have h1 : ∫ z, wordComp w f k z * wordComp w f k z ∂(volume.restrict (Cyl.cell c)) ≤
      ∑ l : Fin 2, ∫ z, wordComp w f l z * wordComp w f l z ∂(volume.restrict (Cyl.cell c)) :=
    Finset.single_le_sum (f := fun l : Fin 2 =>
      ∫ z, wordComp w f l z * wordComp w f l z ∂(volume.restrict (Cyl.cell c)))
      (fun l _ => integral_nonneg (fun z => mul_self_nonneg _)) (Finset.mem_univ k)
  have h2 : ∑ l : Fin 2, ∫ z, wordComp w f l z * wordComp w f l z ∂(volume.restrict (Cyl.cell c)) ≤
      ∑ v ∈ wordsOfLength j, ∑ l : Fin 2,
        ∫ z, wordComp v f l z * wordComp v f l z ∂(volume.restrict (Cyl.cell c)) :=
    Finset.single_le_sum (f := fun v : List Bool => ∑ l : Fin 2,
      ∫ z, wordComp v f l z * wordComp v f l z ∂(volume.restrict (Cyl.cell c)))
      (fun v _ => Finset.sum_nonneg (fun l _ => integral_nonneg (fun z => mul_self_nonneg _)))
      hw
  exact h1.trans h2

/-- Pointwise: the operator norm of the `j`-th derivative of a `Vec`-valued field is bounded by
the sum of the absolute coordinate word derivatives over `wordsOfLength j × Fin 2`. -/
lemma jl2_pointwise (j : ℕ) (f : Plane → Vec) (hf : ContDiff ℝ ∞ f) (z : Plane) :
    ‖iteratedFDeriv ℝ j f z‖ ≤
      ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)), |wordComp i.1 f i.2 z| := by
  have hk : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => f x k) := fun k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hf
  have hpt := UnforcedLeray.Short.Spine.norm_iteratedFDeriv_euclid2_le hf j z
  have h0 : ‖iteratedFDeriv ℝ j (fun x => f x 0) z‖ ≤
      ∑ w ∈ wordsOfLength j, |wordComp w f 0 z| :=
    (cylJetWord_proof (fun x => f x 0) (hk 0) j z).2
  have h1 : ‖iteratedFDeriv ℝ j (fun x => f x 1) z‖ ≤
      ∑ w ∈ wordsOfLength j, |wordComp w f 1 z| :=
    (cylJetWord_proof (fun x => f x 1) (hk 1) j z).2
  rw [Finset.sum_product]
  simp only [Fin.sum_univ_two]
  rw [Finset.sum_add_distrib]
  linarith

theorem jetL2Bridge_proof : JetL2Bridge := by
  intro j
  refine ⟨2 * 2 ^ j, by positivity, ?_⟩
  intro c _hc f hf
  have hsm : ContDiff ℝ ∞ f := hf.1
  have hcard : ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) ≤ 2 * 2 ^ j := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hW : (wordsOfLength j).card ≤ 2 ^ j := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
        _ = 2 ^ j := by simp
    have hW' : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by exact_mod_cast hW
    push_cast
    linarith
  have hsq : 0 ≤ Real.sqrt (jetEnergy c j f) := Real.sqrt_nonneg _
  have hterm : ∀ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
      eLpNorm (fun z => |wordComp i.1 f i.2 z|) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal (Real.sqrt (jetEnergy c j f)) := by
    intro i hi
    rw [Finset.mem_product] at hi
    rw [jl2_abs_eLpNorm _ _ (hf.2.2 i.1 i.2)]
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    exact jl2_energy_le c j f hf i.1 hi.1 i.2
  have hmono : eLpNorm (fun z => iteratedFDeriv ℝ j f z) 2 (Cyl.cellμ c) ≤
      eLpNorm (fun z => ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        |wordComp i.1 f i.2 z|) 2 (Cyl.cellμ c) := by
    apply eLpNorm_mono
    intro z
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    exact jl2_pointwise j f hsm z
  have hsum : eLpNorm (fun z => ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
      |wordComp i.1 f i.2 z|) 2 (Cyl.cellμ c) ≤
      ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        eLpNorm (fun z => |wordComp i.1 f i.2 z|) 2 (Cyl.cellμ c) := by
    have := eLpNorm_sum_le (μ := Cyl.cellμ c) (p := 2)
      (f := fun (i : List Bool × Fin 2) (z : Plane) => |wordComp i.1 f i.2 z|)
      (s := wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)))
      (fun i _ => by
        simpa [Real.norm_eq_abs] using (hf.2.2 i.1 i.2).aestronglyMeasurable.norm)
      one_le_two
    simpa only [Finset.sum_fn] using this
  calc Train.cellL2 c (Train.jet j f)
      = eLpNorm (fun z => iteratedFDeriv ℝ j f z) 2 (Cyl.cellμ c) := rfl
    _ ≤ eLpNorm (fun z => ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        |wordComp i.1 f i.2 z|) 2 (Cyl.cellμ c) := hmono
    _ ≤ ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        eLpNorm (fun z => |wordComp i.1 f i.2 z|) 2 (Cyl.cellμ c) := hsum
    _ ≤ ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        ENNReal.ofReal (Real.sqrt (jetEnergy c j f)) := Finset.sum_le_sum hterm
    _ = ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ≥0∞) *
        ENNReal.ofReal (Real.sqrt (jetEnergy c j f)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) *
        Real.sqrt (jetEnergy c j f)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * 2 ^ j * Real.sqrt (jetEnergy c j f)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hsq)

end UnforcedLeray.Short.PartI
