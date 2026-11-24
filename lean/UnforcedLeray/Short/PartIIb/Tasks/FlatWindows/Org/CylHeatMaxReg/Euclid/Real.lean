import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_1
import UnforcedLeray.Lib.ParabolicB

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The second factor `ℝ × ℝ ≃L Euc 2`. -/
def chmL2 : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

/-- The linear isomorphism `Coord ≃L PS 2`, `(s, (q, η)) ↦ (s, (q, η))`. -/
def chmL : Coord ≃L[ℝ] UnforcedLeray.Parabolic.PS 2 :=
  ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) chmL2

/-- The same map as a measurable equivalence. -/
def chmE : Coord ≃ᵐ UnforcedLeray.Parabolic.PS 2 :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ)).symm).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))

theorem chmE_eq (x : Coord) : chmE x = chmL x := rfl

theorem chmE_mp : MeasurePreserving chmE volume volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm volume volume :=
    MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)
  have h2 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) volume volume := by
    simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod h2).comp
    ((MeasurePreserving.id (volume : Measure ℝ)).prod h1)

theorem chmE_symm_mp : MeasurePreserving chmE.symm volume volume :=
  MeasurePreserving.symm _ chmE_mp

theorem chm_cdir0 : chmL (cdir 0) = UnforcedLeray.Parabolic.tdir := by
  simp [chmL, chmL2, cdir, UnforcedLeray.Parabolic.tdir]

theorem chm_cdir_succ (i : Fin 2) : chmL (cdir i.succ) = UnforcedLeray.Parabolic.sdir i := by
  fin_cases i <;> refine Prod.ext ?_ ?_ <;>
    simp [chmL, chmL2, cdir, UnforcedLeray.Parabolic.sdir, UnforcedLeray.Parabolic.ev] <;>
    (ext k; fin_cases k <;> simp)

theorem chm_cpd_comp (ψ : UnforcedLeray.Parabolic.PS 2 → ℝ) (hψ : Differentiable ℝ ψ) (j : Fin 3)
    (x : Coord) :
    cpd j (fun y => ψ (chmL y)) x = fderiv ℝ ψ (chmL x) (chmL (cdir j)) := by
  unfold cpd
  have h : (fun y => ψ (chmL y)) = ψ ∘ chmL := rfl
  rw [h, fderiv_comp x (hψ (chmL x)) chmL.differentiableAt, chmL.fderiv]
  rfl

theorem chm_cpd0 (ψ : UnforcedLeray.Parabolic.PS 2 → ℝ) (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 0 (fun y => ψ (chmL y)) x = UnforcedLeray.Parabolic.tD ψ (chmL x) := by
  rw [chm_cpd_comp ψ hψ, chm_cdir0]
  rfl

theorem chm_cpd_succ (ψ : UnforcedLeray.Parabolic.PS 2 → ℝ) (hψ : Differentiable ℝ ψ) (i : Fin 2)
    (x : Coord) :
    cpd i.succ (fun y => ψ (chmL y)) x = UnforcedLeray.Parabolic.sD i ψ (chmL x) := by
  rw [chm_cpd_comp ψ hψ, chm_cdir_succ]
  rfl

theorem chm_cpd1 (ψ : UnforcedLeray.Parabolic.PS 2 → ℝ) (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 1 (fun y => ψ (chmL y)) x = UnforcedLeray.Parabolic.sD 0 ψ (chmL x) :=
  chm_cpd_succ ψ hψ 0 x

theorem chm_cpd2 (ψ : UnforcedLeray.Parabolic.PS 2 → ℝ) (hψ : Differentiable ℝ ψ) (x : Coord) :
    cpd 2 (fun y => ψ (chmL y)) x = UnforcedLeray.Parabolic.sD 1 ψ (chmL x) :=
  chm_cpd_succ ψ hψ 1 x

theorem chm_cylHeat (ν : ℝ) {ψ : UnforcedLeray.Parabolic.PS 2 → ℝ}
    (hψ : UnforcedLeray.Parabolic.IsSTTest ψ) (x : Coord) :
    cylHeatT ν (fun y => ψ (chmL y)) x =
      -UnforcedLeray.Parabolic.tD ψ (chmL x) - ν * UnforcedLeray.Parabolic.sLap ψ (chmL x) := by
  have hd : Differentiable ℝ ψ := hψ.differentiable
  have hd0 : Differentiable ℝ (UnforcedLeray.Parabolic.sD 0 ψ) :=
    (hψ.dirD (UnforcedLeray.Parabolic.sdir 0)).differentiable
  have hd1 : Differentiable ℝ (UnforcedLeray.Parabolic.sD 1 ψ) :=
    (hψ.dirD (UnforcedLeray.Parabolic.sdir 1)).differentiable
  have h1 : (fun y => cpd 1 (fun z => ψ (chmL z)) y) =
      fun y => UnforcedLeray.Parabolic.sD 0 ψ (chmL y) :=
    funext fun y => chm_cpd1 ψ hd y
  have h2 : (fun y => cpd 2 (fun z => ψ (chmL z)) y) =
      fun y => UnforcedLeray.Parabolic.sD 1 ψ (chmL y) :=
    funext fun y => chm_cpd2 ψ hd y
  unfold cylHeatT
  rw [h1, h2, chm_cpd0 ψ hd x, chm_cpd1 _ hd0 x, chm_cpd2 _ hd1 x]
  simp only [UnforcedLeray.Parabolic.sLap, Fin.sum_univ_two]

theorem chm_isSTTestCoord {ψ : UnforcedLeray.Parabolic.PS 2 → ℝ}
    (hψ : UnforcedLeray.Parabolic.IsSTTest ψ) : IsSTTestCoord (fun x => ψ (chmL x)) :=
  ⟨hψ.1.comp chmL.contDiff, hψ.2.comp_homeomorph chmL.toHomeomorph⟩

theorem chm_isSTTest_of_coord {φ : Coord → ℝ} (hφ : IsSTTestCoord φ) :
    UnforcedLeray.Parabolic.IsSTTest (fun X => φ (chmL.symm X)) :=
  ⟨hφ.smooth.comp chmL.symm.contDiff, hφ.compact.comp_homeomorph chmL.symm.toHomeomorph⟩

theorem chm_int_comp (f : UnforcedLeray.Parabolic.PS 2 → ℝ) :
    ∫ x, f (chmL x) = ∫ X, f X :=
  chmE_mp.integral_comp' f

theorem chm_integral_transport (u : Coord → ℝ) (g : UnforcedLeray.Parabolic.PS 2 → ℝ) :
    ∫ x, u x * g (chmL x) = ∫ X, (u ∘ chmE.symm) X * g X := by
  rw [← chm_int_comp (fun X => (u ∘ chmE.symm) X * g X)]
  congr 1

theorem chm_eLpNorm_fwd (g : UnforcedLeray.Parabolic.PS 2 → ℝ) (hg : AEStronglyMeasurable g volume)
    (p : ℝ≥0∞) : eLpNorm (fun x => g (chmL x)) p volume = eLpNorm g p volume :=
  eLpNorm_comp_measurePreserving hg chmE_mp

theorem chm_eLpNorm_symm (u : Coord → ℝ) (hu : AEStronglyMeasurable u volume) (p : ℝ≥0∞) :
    eLpNorm (u ∘ chmE.symm) p volume = eLpNorm u p volume :=
  eLpNorm_comp_measurePreserving hu chmE_symm_mp

end UnforcedLeray.Short.IIb

open UnforcedLeray.Short.IIb MeasureTheory
open scoped ENNReal

theorem chmEuclidReal : UnforcedLeray.Short.IIb.ChmEuclidReal := by
  unfold UnforcedLeray.Short.IIb.ChmEuclidReal
  intro r hr
  obtain ⟨Cd, hCd⟩ := UnforcedLeray.Parabolic.heat_maximal_regularity (d := 2) hr
  refine ⟨(Cd : ℝ) + 1, by positivity, ?_⟩
  unfold UnforcedLeray.Short.IIb.ChmEuclidRealAt
  intro ν hν u F hu hF hur hFr heq
  have hur' : MemLp u (ENNReal.ofReal r) volume := ⟨hu, hur⟩
  have hFr' : MemLp F (ENNReal.ofReal r) volume := ⟨hF, hFr⟩
  have hut : MemLp (u ∘ chmE.symm) (ENNReal.ofReal r) volume :=
    hur'.comp_measurePreserving chmE_symm_mp
  have hFt : MemLp (F ∘ chmE.symm) (ENNReal.ofReal r) volume :=
    hFr'.comp_measurePreserving chmE_symm_mp
  have hweak : ∀ φ : UnforcedLeray.Parabolic.PS 2 → ℝ, UnforcedLeray.Parabolic.IsSTTest φ →
      ∫ X, (u ∘ chmE.symm) X * (-UnforcedLeray.Parabolic.tD φ X -
        ν * UnforcedLeray.Parabolic.sLap φ X) = ∫ X, (F ∘ chmE.symm) X * φ X := by
    intro φ hφ
    have key : ∫ x, u x * (-UnforcedLeray.Parabolic.tD φ (chmL x) -
        ν * UnforcedLeray.Parabolic.sLap φ (chmL x)) = ∫ x, F x * φ (chmL x) := by
      have h := heq _ (chm_isSTTestCoord hφ)
      simp only [chm_cylHeat ν hφ] at h
      exact h
    rw [← chm_integral_transport u (fun X => -UnforcedLeray.Parabolic.tD φ X -
        ν * UnforcedLeray.Parabolic.sLap φ X), ← chm_integral_transport F φ]
    exact key
  obtain ⟨D2', Dt', hD2, hDt, hDtw, hD2b, hDtb⟩ := hCd hν hut hFt hweak
  have hDtψ : ∀ ψ : UnforcedLeray.Parabolic.PS 2 → ℝ, UnforcedLeray.Parabolic.IsSTTest ψ →
      ∫ x, u x * cpd 0 (fun y => ψ (chmL y)) x = -∫ x, Dt' (chmL x) * ψ (chmL x) := by
    intro ψ hψ
    simp only [chm_cpd0 ψ hψ.differentiable]
    rw [chm_integral_transport u (fun X => UnforcedLeray.Parabolic.tD ψ X),
      chm_int_comp (fun X => Dt' X * ψ X)]
    exact hDtw ψ hψ
  have hD2ψ : ∀ i j : Fin 2, ∀ ψ : UnforcedLeray.Parabolic.PS 2 → ℝ,
      UnforcedLeray.Parabolic.IsSTTest ψ →
      ∫ x, u x * cpd i.succ (fun y => cpd j.succ (fun z => ψ (chmL z)) y) x =
        ∫ x, D2' i j (chmL x) * ψ (chmL x) := by
    intro i j ψ hψ
    have hdj : Differentiable ℝ (UnforcedLeray.Parabolic.sD j ψ) :=
      (hψ.dirD (UnforcedLeray.Parabolic.sdir j)).differentiable
    have h1 : (fun y => cpd j.succ (fun z => ψ (chmL z)) y) =
        fun y => UnforcedLeray.Parabolic.sD j ψ (chmL y) :=
      funext fun y => chm_cpd_succ ψ hψ.differentiable j y
    rw [h1]
    simp only [chm_cpd_succ _ hdj]
    rw [chm_integral_transport u (fun X => UnforcedLeray.Parabolic.sD i
        (UnforcedLeray.Parabolic.sD j ψ) X), chm_int_comp (fun X => D2' i j X * ψ X)]
    exact (hD2 i j).2 ψ hψ
  refine ⟨fun x => Dt' (chmL x), fun i j x => D2' i j (chmL x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hDt.1.comp_measurePreserving chmE_mp
  · intro i j
    exact (hD2 i j).1.1.comp_measurePreserving chmE_mp
  · intro φ hφ
    have h := hDtψ (fun X => φ (chmL.symm X)) (chm_isSTTest_of_coord hφ)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    exact h
  · intro i j φ hφ
    have h := hD2ψ i j (fun X => φ (chmL.symm X)) (chm_isSTTest_of_coord hφ)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    exact h
  · have hp : ENNReal.ofReal ((Cd : ℝ) + 1) = ENNReal.ofReal ((Cd : ℝ) + 1) := rfl
    calc eLpNorm (fun x => Dt' (chmL x)) (ENNReal.ofReal r) volume
        = eLpNorm Dt' (ENNReal.ofReal r) volume :=
          chm_eLpNorm_fwd Dt' hDt.1 _
      _ ≤ (Cd : ℝ≥0∞) * eLpNorm (F ∘ chmE.symm) (ENNReal.ofReal r) volume := hDtb
      _ = (Cd : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal r) volume := by
          rw [chm_eLpNorm_symm F hF]
      _ ≤ ENNReal.ofReal ((Cd : ℝ) + 1) * eLpNorm F (ENNReal.ofReal r) volume := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro i j
    show eLpNorm (fun x => ν * D2' i j (chmL x)) (ENNReal.ofReal r) volume ≤ _
    calc eLpNorm (fun x => ν * D2' i j (chmL x)) (ENNReal.ofReal r) volume
        = eLpNorm (fun X => ν * D2' i j X) (ENNReal.ofReal r) volume :=
          chm_eLpNorm_fwd (fun X => ν * D2' i j X) (((hD2 i j).1.1).const_mul ν) _
      _ ≤ (Cd : ℝ≥0∞) * eLpNorm F (ENNReal.ofReal r) volume := by
          rw [← chm_eLpNorm_symm F hF]
          exact hD2b i j
      _ ≤ ENNReal.ofReal ((Cd : ℝ) + 1) * eLpNorm F (ENNReal.ofReal r) volume := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith)
