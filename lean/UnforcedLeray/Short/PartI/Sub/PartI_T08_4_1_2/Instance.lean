import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2.L2SqDeriv
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.SliceWordTimeComm
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Part I, task `PartI:T08/4/1/2/2` (`TrainWordEnergyHasDerivAt`): proof

Source `the November 2 reference manuscript` lines 341-348.
Applies the generic `L²` lemma `l2Sq_hasDerivAt` to `F r z = ∂_w e_k(r, z)` on the cell.
Time-localisation `loc` makes `r ↦ F r z` globally `C¹` (the train is only smooth for `t ≥ 0`).
Time and word derivatives commute by `swtc_main`; joint smoothness of `e` on `(0, ∞) × ℝ²`
comes from `IsTrain.smooth_v` and `IIb.vcSmooth_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI.TrainWordEnergyInstance

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- Time localisation: equal to `t` for `t > 3s/4`, equal to `s` for `t ≤ s/2`. -/
def loc (s t : ℝ) : ℝ := s + Real.smoothTransition ((t - s / 2) / (s / 4)) * (t - s)

theorem loc_self (s : ℝ) : loc s s = s := by
  unfold loc; ring

theorem loc_eq_id {s t : ℝ} (hs0 : 0 < s) (h : 3 * s / 4 < t) : loc s t = t := by
  unfold loc
  have hs : (0:ℝ) < s / 4 := by linarith
  have h1 : (1 : ℝ) ≤ (t - s / 2) / (s / 4) := by
    rw [le_div_iff₀ hs]; linarith
  rw [Real.smoothTransition.one_of_one_le h1]; ring

theorem loc_pos {s : ℝ} (hs : 0 < s) (t : ℝ) : 0 < loc s t := by
  unfold loc
  have h0 := Real.smoothTransition.nonneg ((t - s / 2) / (s / 4))
  have h1 := Real.smoothTransition.le_one ((t - s / 2) / (s / 4))
  by_cases ht : t ≤ s / 2
  · have hle : (t - s / 2) / (s / 4) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    rw [Real.smoothTransition.zero_of_nonpos hle]
    linarith
  · simp only [not_le] at ht
    nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ t - s / 2),
      mul_nonneg (sub_nonneg.2 h1) hs.le, mul_nonneg h0 hs.le]

theorem contDiff_loc (s : ℝ) : ContDiff ℝ ∞ (loc s) := by
  have hst : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (t - s / 2) / (s / 4)) := by fun_prop
  have hg : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t - s / 2) / (s / 4))) :=
    hst.comp hf
  exact contDiff_const.add (hg.mul (contDiff_id.sub contDiff_const))

/-- Joint smoothness of the velocity error on `(0, ∞) × ℝ²`. -/
theorem trainErr_contDiffOn {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => trainErr tr x.1 x.2) (Ioi 0 ×ˢ univ) := by
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self subset_rfl)
  have hV : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Vc ν c x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.IIb.vcSmooth_proof ν c hν (by linarith)
  exact hv.sub hV

/-- Joint smoothness of the `k`-th component. -/
theorem trainErr_comp_contDiffOn {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (k : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => trainErr tr x.1 x.2 k) (Ioi 0 ×ˢ univ) := by
  have hproj : ContDiff ℝ ∞ (fun y : Vec => (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) y) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff
  exact hproj.comp_contDiffOn (trainErr_contDiffOn hν hc tr)

theorem trainErr_diffAt {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (z : Plane) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun τ => trainErr tr τ z) t := by
  have hO : IsOpen (Ioi (0:ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hmem : (t, z) ∈ Ioi (0:ℝ) ×ˢ (univ : Set Plane) := ⟨ht, mem_univ z⟩
  have h1 : DifferentiableAt ℝ (fun x : ℝ × Plane => trainErr tr x.1 x.2) (t, z) :=
    ((trainErr_contDiffOn hν hc tr).contDiffAt (hO.mem_nhds hmem)).differentiableAt
      (by simp)
  have h2 : DifferentiableAt ℝ (fun τ : ℝ => (τ, z)) t :=
    differentiableAt_id.prodMk (differentiableAt_const z)
  exact DifferentiableAt.comp (𝕜 := ℝ) (g := fun x : ℝ × Plane => trainErr tr x.1 x.2)
    (f := fun τ : ℝ => (τ, z)) t h1 h2

theorem deriv_comp_proj {g : ℝ → Vec} {t : ℝ} (hg : DifferentiableAt ℝ g t) (k : Fin 2) :
    deriv (fun τ => g τ k) t = deriv g t k := by
  have hL : HasDerivAt (fun τ => (EuclideanSpace.proj k : Vec →L[ℝ] ℝ) (g τ))
      ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ) (deriv g t)) t :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hg.hasDerivAt
  exact hL.deriv

theorem wordComp_time_smooth {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (w : List Bool) (k : Fin 2) (z : Plane) :
    ContDiffOn ℝ ∞ (fun τ => wordComp w (trainErr tr τ) k z) (Ioi 0) := by
  have hF := trainErr_comp_contDiffOn hν hc tr k
  have hW : ContDiffOn ℝ ∞ (swtcWord w (fun p : ℝ × Plane => trainErr tr p.1 p.2 k)) swtcO :=
    swtc_sm w _ hF
  have hline : ContDiffOn ℝ ∞ (fun τ : ℝ => (τ, z)) (Ioi 0) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : MapsTo (fun τ : ℝ => (τ, z)) (Ioi 0) swtcO := fun τ hτ => ⟨hτ, mem_univ z⟩
  have hc2 := hW.comp hline hmaps
  refine hc2.congr (fun τ hτ => ?_)
  exact swtc_slice w _ hF τ hτ z

theorem wordComp_time_deriv {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (w : List Bool) (k : Fin 2) {t : ℝ} (ht : 0 < t) (z : Plane) :
    deriv (fun τ => wordComp w (trainErr tr τ) k z) t =
      wordComp w (fun y => deriv (fun τ => trainErr tr τ y) t) k z := by
  have hF := trainErr_comp_contDiffOn hν hc tr k
  have key : deriv (fun τ => B0151.derivWord w (fun z' => trainErr tr τ z' k) z) t =
      B0151.derivWord w (fun z' => deriv (fun τ => trainErr tr τ z' k) t) z :=
    swtc_main (fun p : ℝ × Plane => trainErr tr p.1 p.2 k) hF w t z ht
  have hfun : (fun z' => deriv (fun τ => trainErr tr τ z' k) t) =
      fun y => deriv (fun τ => trainErr tr τ y) t k := by
    funext y
    exact deriv_comp_proj (g := fun τ => trainErr tr τ y) (trainErr_diffAt hν hc tr y ht) k
  rw [hfun] at key
  exact key

theorem wordComp_loc_deriv {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (w : List Bool) (k : Fin 2) {s r : ℝ} (hs : 0 < s) (hr : 3 * s / 4 < r) (z : Plane) :
    deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) r =
      wordComp w (fun y => deriv (fun τ => trainErr tr τ y) r) k z := by
  have hev : (fun t => wordComp w (trainErr tr (loc s t)) k z) =ᶠ[𝓝 r]
      (fun t => wordComp w (trainErr tr t) k z) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    rw [loc_eq_id hs ht]
  rw [hev.deriv_eq]
  exact wordComp_time_deriv hν hc tr w k (t := r) (by linarith) z

end UnforcedLeray.Short.PartI.TrainWordEnergyInstance

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Short.PartI.TrainWordEnergyInstance
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **`TrainWordEnergyHasDerivAt` (Part I, task `PartI:T08/4/1/2/2`).** -/
theorem trainWordEnergyHasDerivAt_proof :
    UnforcedLeray.Short.PartI.TrainWordEnergyHasDerivAt := by
  intro hloc ν c hν hc tr htr s hs hw w k
  obtain ⟨ε0, hε0, K0, hK⟩ := hloc ν c hν hc tr htr s hs hw w k
  have hεpos : 0 < min ε0 (s / 4) := lt_min hε0 (by linarith)
  have hC : ∀ z, ContDiff ℝ 1 (fun r => wordComp w (trainErr tr (loc s r)) k z) := fun z =>
    ContDiffOn.comp_contDiff ((wordComp_time_smooth hν hc tr w k z).of_le
      (by exact_mod_cast le_top)) ((contDiff_loc s).of_le (by exact_mod_cast le_top))
      (fun x => loc_pos hs x)
  have hF : MemLp (fun z => wordComp w (trainErr tr (loc s s)) k z) 2 (Cyl.cellμ c) := by
    rw [loc_self]
    exact trainErrJetL2_proof ν c hν hc tr htr s hs hw w k
  have hD : ∀ r, |r - s| < min ε0 (s / 4) →
      MemLp (fun z => deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) r) 2
        (Cyl.cellμ c) ∧
      ∫ z, (deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) r) ^ 2 ∂(Cyl.cellμ c)
        ≤ K0 := by
    intro r hr
    have hr1 : |r - s| < ε0 := lt_of_lt_of_le hr (min_le_left _ _)
    have hr2 : |r - s| < s / 4 := lt_of_lt_of_le hr (min_le_right _ _)
    have hr34 : 3 * s / 4 < r := by have := (abs_lt.1 hr2).1; linarith
    obtain ⟨hm, hint⟩ := hK r (by linarith) hr1
    simp only [wordComp_loc_deriv hν hc tr w k hs hr34]
    exact ⟨hm, hint⟩
  have hG : (∀ᶠ r in 𝓝 s, MemLp (fun z => wordComp w (trainErr tr (loc s r)) k z) 2
      (Cyl.cellμ c)) ∧
      HasDerivAt (fun r => ∫ z, (wordComp w (trainErr tr (loc s r)) k z) ^ 2 ∂(Cyl.cellμ c))
        (2 * ∫ z, wordComp w (trainErr tr (loc s s)) k z *
          deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) s ∂(Cyl.cellμ c)) s :=
    UnforcedLeray.Short.PartI.L2SqDeriv.l2Sq_hasDerivAt (μ := Cyl.cellμ c)
      (fun r z => wordComp w (trainErr tr (loc s r)) k z) s (min ε0 (s / 4)) K0 hεpos hC hF hD
  obtain ⟨hev, hder⟩ := hG
  have hs34 : 3 * s / 4 < s := by linarith
  have hV : (2 * ∫ z, wordComp w (trainErr tr (loc s s)) k z *
      deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) s ∂(Cyl.cellμ c)) =
      2 * ∫ z in Cyl.cell c, wordComp w (trainErr tr s) k z *
        wordComp w (fun y => deriv (fun t => trainErr tr t y) s) k z := by
    congr 2
    funext z
    rw [loc_self, wordComp_loc_deriv hν hc tr w k hs hs34 z]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hev, Ioi_mem_nhds hs34] with r hr hr2
    rw [loc_eq_id hs hr2] at hr
    exact hr
  · exact (hK s hs (by simp [hε0])).1
  · have hfuneq : (fun r => ∫ z in Cyl.cell c, (wordComp w (trainErr tr r) k z) ^ 2) =ᶠ[𝓝 s]
        (fun r => ∫ z in Cyl.cell c, (wordComp w (trainErr tr (loc s r)) k z) ^ 2) := by
      filter_upwards [Ioi_mem_nhds hs34] with r hr
      rw [loc_eq_id hs hr]
    rw [← hV]
    exact hder.congr_of_eventuallyEq hfuneq


end UnforcedLeray.Short.PartI
