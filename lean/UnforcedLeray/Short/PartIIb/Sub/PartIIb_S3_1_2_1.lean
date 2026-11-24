import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.MorreyL4
import UnforcedLeray.Lib.LerayC.WeakDeriv

/-!
# `PartII-b:S3/1/2/1` decomposition (`Sub/PartII-b_S3_1_2_1.lean`, SP 2552, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2552 and 2559-2562:
"These estimates are uniform in phase; the bounded Cartesian Leray map preserves them in $W^{k,p}$.
... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives".

## Proved here (zero `sorry`)

1. **Linearity of `IsSmoothLerayRep` and `smoothLerayProj`**:
   - `isSmoothLerayRep_zero`, `smoothLerayProj_zero`;
   - `isSmoothLerayRep_smul`, `smoothLerayProj_smul`, `isSmoothLerayRep_neg`, `isSmoothLerayRep_sub`,
     `smoothLerayProj_sub`;
   - `isSmoothLerayRep_sum`, `smoothLerayProj_sum`.
2. **Directional spatial jets in `L⁴(ℝ³)` and weak spatial derivative uniqueness**:
   - `memLp_dirSpatialJet_of_memLp_iteratedFDeriv`, `eLpNorm_dirSpatialJet_le`;
   - `hasWeakSpatialDerivative_dirSpatialJet`: classical directional jets of `C^∞` spatial fields
     are weak spatial derivatives (`HasWeakSpatialDerivative`);
   - `hasWeakSpatialDerivative_ae_unique`: uniqueness a.e. of weak spatial derivatives in `L⁴(ℝ³)`
     via `RieszLp.hasDerivAt_shiftLp` and `HasDerivAt.unique`.
3. **Commutation of `IsSmoothLerayRep` and `smoothLerayProj` with all spatial directional jets**:
   - `isSmoothLerayRep_dirSpatialJet`: by induction on `ws : List Space` using
     `RieszLp.lerayLp_toLp_hasWeakSpatialDerivative`, `hasWeakSpatialDerivative_ae_unique`, and
     coordinate expansion `w = ∑ i : Fin 3, w i • coordinateVector i`;
   - `smoothLerayProj_dirSpatialJet` and `smoothLeraySlice_dirSpatialJet`:
     `dirSpatialJet (smoothLerayProj f) ws = smoothLerayProj (dirSpatialJet f ws)`.
4. **All-order `W^{k,4}(ℝ³) ∩ W^{k,∞}(ℝ³)` bounds on `smoothLeraySlice F`**:
   - `norm_iteratedFDeriv_succ_le_sum_dirSpatialJet`: for every smooth `F : SpatialField`,
     `‖iteratedFDeriv ℝ (k + 1) F y‖ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y‖`;
   - `eLpNorm_iteratedFDeriv_lerayRep_le`: by induction on `k : ℕ`,
     `eLpNorm (fun y => iteratedFDeriv ℝ k g y) 4 volume ≤ (3 : ℝ≥0∞) ^ k * ‖RieszLp.lerayLp 4 _ _‖₊ * eLpNorm (fun y => iteratedFDeriv ℝ k f y) 4 volume`;
   - `sliceFamily_smoothLeraySlice_of_repExists`: combines `eLpNorm_iteratedFDeriv_lerayRep_le` with
     the proved 3D Morrey inequality `smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof`
     (`isUniformSmoothL4SliceFamily_of_morreyL4`) to establish Conjunct 1 of
     `SmoothLeraySliceRegularity` from `SmoothLerayRepExists`;
   - `hasPhaseJetDeriv_smoothLeraySlice_of_zero`: reduces Conjunct 2 of
     `SmoothLeraySliceRegularity` across all iterated spatial directional jets `ws : List Space` to
     the `ws = []` case `SmoothLeraySliceDerivZero`.
5. **Conditional assembly `smoothLeraySliceRegularity_of`** of `SmoothLeraySliceRegularity` from
   `SmoothLerayRepExists` (`PartII-b:S3/1/2/1/1`) and `SmoothLeraySliceDerivZero`
   (`PartII-b:S3/1/2/1/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

local instance fact_one_le_four_sls : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace SmoothLeraySliceSub

/-! ## 1. Linearity of `IsSmoothLerayRep` and `smoothLerayProj` -/

theorem isSmoothLerayRep_zero :
    IsSmoothLerayRep 0 0 := by
  refine ⟨MemLp.zero, contDiff_const, ?_⟩
  set P := UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)
  have htoLp : (MemLp.zero : MemLp (0 : SpatialField) 4 volume).toLp 0 = 0 := MemLp.toLp_zero _
  have hmap : P ((MemLp.zero : MemLp (0 : SpatialField) 4 volume).toLp 0) = 0 := by
    rw [htoLp, map_zero]
  rw [hmap]
  exact (Lp.coeFn_zero Space 4 (volume : Measure Space)).symm

@[simp]
theorem smoothLerayProj_zero :
    smoothLerayProj 0 = 0 :=
  HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep isSmoothLerayRep_zero

theorem isSmoothLerayRep_smul (c : ℝ) {F G : SpatialField}
    (h : IsSmoothLerayRep F G) :
    IsSmoothLerayRep (c • F) (c • G) := by
  obtain ⟨hF, hG, heq⟩ := h
  refine ⟨hF.const_smul c, hG.const_smul c, ?_⟩
  set P := UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)
  have htoLp : (hF.const_smul c).toLp (c • F) = c • hF.toLp F :=
    MemLp.toLp_const_smul c hF
  have hmap : P ((hF.const_smul c).toLp (c • F)) = c • P (hF.toLp F) := by
    rw [htoLp, map_smul]
  have hcoe := Lp.coeFn_smul c (P (hF.toLp F))
  refine (heq.const_smul c).trans ?_
  rw [hmap]
  exact hcoe.symm

theorem smoothLerayProj_smul (c : ℝ) {F : SpatialField}
    (h : IsSmoothLerayRep F (smoothLerayProj F)) :
    smoothLerayProj (c • F) = c • smoothLerayProj F :=
  HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep (isSmoothLerayRep_smul c h)

theorem isSmoothLerayRep_neg {F G : SpatialField}
    (h : IsSmoothLerayRep F G) :
    IsSmoothLerayRep (-F) (-G) := by
  simpa [neg_one_smul] using isSmoothLerayRep_smul (-1 : ℝ) h

theorem isSmoothLerayRep_sub {F₁ F₂ G₁ G₂ : SpatialField}
    (h₁ : IsSmoothLerayRep F₁ G₁) (h₂ : IsSmoothLerayRep F₂ G₂) :
    IsSmoothLerayRep (F₁ - F₂) (G₁ - G₂) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact HigherPhaseSub.isSmoothLerayRep_add h₁ (isSmoothLerayRep_neg h₂)

theorem smoothLerayProj_sub {F₁ F₂ : SpatialField}
    (h₁ : IsSmoothLerayRep F₁ (smoothLerayProj F₁))
    (h₂ : IsSmoothLerayRep F₂ (smoothLerayProj F₂)) :
    smoothLerayProj (F₁ - F₂) = smoothLerayProj F₁ - smoothLerayProj F₂ :=
  HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep (isSmoothLerayRep_sub h₁ h₂)

theorem isSmoothLerayRep_sum {ι : Type*} (s : Finset ι) {F G : ι → SpatialField}
    (h : ∀ i ∈ s, IsSmoothLerayRep (F i) (G i)) :
    IsSmoothLerayRep (fun y => ∑ i ∈ s, F i y) (fun y => ∑ i ∈ s, G i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun _ : Space => (0 : Space)) = (0 : SpatialField) := rfl
      simpa [h0] using isSmoothLerayRep_zero
  | @insert a s ha ih =>
      have ha_rep := h a (Finset.mem_insert_self a s)
      have hs_rep := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hF_eq : (fun y => ∑ i ∈ insert a s, F i y) =
          F a + (fun y => ∑ i ∈ s, F i y) := by
        funext y; simp [Finset.sum_insert ha]
      have hG_eq : (fun y => ∑ i ∈ insert a s, G i y) =
          G a + (fun y => ∑ i ∈ s, G i y) := by
        funext y; simp [Finset.sum_insert ha]
      rw [hF_eq, hG_eq]
      exact HigherPhaseSub.isSmoothLerayRep_add ha_rep hs_rep

theorem smoothLerayProj_sum {ι : Type*} (s : Finset ι) {F : ι → SpatialField}
    (h : ∀ i ∈ s, IsSmoothLerayRep (F i) (smoothLerayProj (F i))) :
    smoothLerayProj (fun y => ∑ i ∈ s, F i y) =
      fun y => ∑ i ∈ s, smoothLerayProj (F i) y :=
  HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep (isSmoothLerayRep_sum s h)

/-! ## 2. Directional spatial jets in `L⁴(ℝ³)` and weak spatial derivatives -/

theorem memLp_iteratedFDeriv_of_sliceFamily {F : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (k : ℕ) (τ : ℝ) :
    MemLp (fun y => iteratedFDeriv ℝ k (F τ) y) 4 volume := by
  obtain ⟨M, hM⟩ := hF.l4_bounded k
  exact ⟨HigherPhaseSub.sliceFamily_aestronglyMeasurable_iteratedFDeriv hF k τ,
    (hM τ).trans_lt ENNReal.ofReal_lt_top⟩

theorem eLpNorm_dirSpatialJet_le {f : SpatialField} (hf : ContDiff ℝ ∞ f) (ws : List Space) :
    eLpNorm (dirSpatialJet f ws) 4 volume ≤
      ENNReal.ofReal (ws.map norm).prod *
        eLpNorm (fun y => iteratedFDeriv ℝ ws.length f y) 4 volume := by
  set P : ℝ := (ws.map norm).prod
  have hP : 0 ≤ P :=
    List.prod_nonneg fun r hr => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.1 hr
      exact norm_nonneg w
  have hpt : ∀ y : Space,
      ‖dirSpatialJet f ws y‖ ≤
        ‖(P • fun y' => iteratedFDeriv ℝ ws.length f y') y‖ := by
    intro y
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hP, mul_comm]
    exact JointSmoothSub.norm_dirSpatialJet_le hf ws y
  calc eLpNorm (dirSpatialJet f ws) 4 volume
      ≤ eLpNorm (P • fun y => iteratedFDeriv ℝ ws.length f y) 4 volume :=
        eLpNorm_mono hpt
    _ = ENNReal.ofReal P *
          eLpNorm (fun y => iteratedFDeriv ℝ ws.length f y) 4 volume := by
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg hP]

theorem memLp_dirSpatialJet_of_memLp_iteratedFDeriv {f : SpatialField}
    (hf : ContDiff ℝ ∞ f) (ws : List Space)
    (hm : MemLp (fun y => iteratedFDeriv ℝ ws.length f y) 4 volume) :
    MemLp (dirSpatialJet f ws) 4 volume := by
  refine ⟨(JointSmoothSub.contDiff_infty_dirSpatialJet hf ws).continuous.aestronglyMeasurable, ?_⟩
  exact (eLpNorm_dirSpatialJet_le hf ws).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm.eLpNorm_lt_top)

/-- For any smooth field `f : SpatialField`, the directional jet
`dirSpatialJet f (coordinateVector i :: ws)` is the `i`-th weak spatial derivative of
`dirSpatialJet f ws`. -/
theorem hasWeakSpatialDerivative_dirSpatialJet {f : SpatialField}
    (hf : ContDiff ℝ ∞ f) (ws : List Space) (i : Fin 3) :
    HasWeakSpatialDerivative i (dirSpatialJet f ws)
      (dirSpatialJet f (coordinateVector i :: ws)) := by
  have hws : ContDiff ℝ 1 (dirSpatialJet f ws) :=
    (JointSmoothSub.contDiff_infty_dirSpatialJet hf ws).of_le (by exact_mod_cast le_top)
  exact hasWeakSpatialDerivative_of_contDiff hws i

/-- Weak spatial derivatives in `L⁴(ℝ³)` are unique almost everywhere. -/
theorem hasWeakSpatialDerivative_ae_unique {i : Fin 3}
    {f₁ f₂ g₁ g₂ : SpatialField}
    (hf₁ : MemLp f₁ 4 volume) (hf₂ : MemLp f₂ 4 volume)
    (hg₁ : MemLp g₁ 4 volume) (hg₂ : MemLp g₂ 4 volume)
    (hfeq : f₁ =ᵐ[volume] f₂)
    (h₁ : HasWeakSpatialDerivative i f₁ g₁)
    (h₂ : HasWeakSpatialDerivative i f₂ g₂) :
    g₁ =ᵐ[volume] g₂ := by
  have hp : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hLp : hf₁.toLp f₁ = hf₂.toLp f₂ := MemLp.toLp_congr hf₁ hf₂ hfeq
  have hd₁ : HasDerivAt (fun s : ℝ => UnforcedLeray.RieszLp.shiftLp 4 i s (hf₁.toLp f₁))
      (hg₁.toLp g₁) 0 :=
    UnforcedLeray.RieszLp.hasDerivAt_shiftLp hp
      (h₁.congr hf₁.coeFn_toLp.symm hg₁.coeFn_toLp.symm)
  have hd₂ : HasDerivAt (fun s : ℝ => UnforcedLeray.RieszLp.shiftLp 4 i s (hf₁.toLp f₁))
      (hg₂.toLp g₂) 0 := by
    rw [hLp]
    exact UnforcedLeray.RieszLp.hasDerivAt_shiftLp hp
      (h₂.congr hf₂.coeFn_toLp.symm hg₂.coeFn_toLp.symm)
  have hG : hg₁.toLp g₁ = hg₂.toLp g₂ := hd₁.unique hd₂
  refine hg₁.coeFn_toLp.symm.trans ?_
  rw [hG]
  exact hg₂.coeFn_toLp

/-! ## 3. Commutation of `IsSmoothLerayRep` with iterated spatial directional jets -/

/-- Coordinate expansion of `dirSpatialJet F (w :: ws)` in the standard basis `coordinateVector i`. -/
theorem dirSpatialJet_cons_eq_sum_coordinates (F : SpatialField) (w : Space) (ws : List Space) :
    dirSpatialJet F (w :: ws) =
      fun y => ∑ i : Fin 3, (w i) • dirSpatialJet F (coordinateVector i :: ws) y := by
  funext y
  dsimp [dirSpatialJet]
  have hw : w = ∑ i : Fin 3, (w i) • coordinateVector i := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-- If `IsSmoothLerayRep f g` holds for smooth fields `f, g : SpatialField` whose iterated spatial
derivatives all lie in `L⁴(ℝ³)`, then `IsSmoothLerayRep (dirSpatialJet f ws) (dirSpatialJet g ws)`
holds for every directional word `ws : List Space`. -/
theorem isSmoothLerayRep_dirSpatialJet {f g : SpatialField}
    (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (hgm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k g y) 4 volume)
    (hrep : IsSmoothLerayRep f g) :
    ∀ ws : List Space, IsSmoothLerayRep (dirSpatialJet f ws) (dirSpatialJet g ws)
  | [] => hrep
  | w :: ws => by
      have ih : IsSmoothLerayRep (dirSpatialJet f ws) (dirSpatialJet g ws) :=
        isSmoothLerayRep_dirSpatialJet hf hfm hgm hrep ws
      obtain ⟨hf_ws, hg_ws, heq_ws⟩ := ih
      have hg : ContDiff ℝ ∞ g := hrep.2.1
      have hcoord : ∀ i : Fin 3,
          IsSmoothLerayRep (dirSpatialJet f (coordinateVector i :: ws))
            (dirSpatialJet g (coordinateVector i :: ws)) := by
        intro i
        have hf_iws : MemLp (dirSpatialJet f (coordinateVector i :: ws)) 4 volume :=
          memLp_dirSpatialJet_of_memLp_iteratedFDeriv hf (coordinateVector i :: ws)
            (hfm (coordinateVector i :: ws).length)
        have hg_iws : MemLp (dirSpatialJet g (coordinateVector i :: ws)) 4 volume :=
          memLp_dirSpatialJet_of_memLp_iteratedFDeriv hg (coordinateVector i :: ws)
            (hgm (coordinateVector i :: ws).length)
        have hg_ws_m : MemLp (dirSpatialJet g ws) 4 volume :=
          memLp_dirSpatialJet_of_memLp_iteratedFDeriv hg ws (hgm ws.length)
        refine ⟨hf_iws,
          JointSmoothSub.contDiff_infty_dirSpatialJet hg (coordinateVector i :: ws), ?_⟩
        set P := UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)
        have hw_f : HasWeakSpatialDerivative i (dirSpatialJet f ws)
            (dirSpatialJet f (coordinateVector i :: ws)) :=
          hasWeakSpatialDerivative_dirSpatialJet hf ws i
        have hw_Pf : HasWeakSpatialDerivative i (P (hf_ws.toLp (dirSpatialJet f ws)) : SpatialField)
            (P (hf_iws.toLp (dirSpatialJet f (coordinateVector i :: ws))) : SpatialField) :=
          UnforcedLeray.RieszLp.lerayLp_toLp_hasWeakSpatialDerivative
            (by norm_num) (by norm_num) hf_ws hf_iws hw_f
        have hw_g : HasWeakSpatialDerivative i (dirSpatialJet g ws)
            (dirSpatialJet g (coordinateVector i :: ws)) :=
          hasWeakSpatialDerivative_dirSpatialJet hg ws i
        exact hasWeakSpatialDerivative_ae_unique hg_ws_m
          (Lp.memLp (P (hf_ws.toLp (dirSpatialJet f ws))))
          hg_iws
          (Lp.memLp (P (hf_iws.toLp (dirSpatialJet f (coordinateVector i :: ws)))))
          heq_ws hw_g hw_Pf
      rw [dirSpatialJet_cons_eq_sum_coordinates f w ws,
        dirSpatialJet_cons_eq_sum_coordinates g w ws]
      exact isSmoothLerayRep_sum Finset.univ fun i _ =>
        isSmoothLerayRep_smul (w i) (hcoord i)

theorem smoothLerayProj_dirSpatialJet {f : SpatialField}
    (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (hgm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k (smoothLerayProj f) y) 4 volume)
    (hrep : IsSmoothLerayRep f (smoothLerayProj f)) (ws : List Space) :
    smoothLerayProj (dirSpatialJet f ws) = dirSpatialJet (smoothLerayProj f) ws :=
  HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep
    (isSmoothLerayRep_dirSpatialJet hf hfm hgm hrep ws)

/-! ## 4. Coordinate bound on `iteratedFDeriv` and `L⁴` bounds on `smoothLerayProj` -/

/-- For any smooth spatial vector field `F : SpatialField`, the norm of `iteratedFDeriv ℝ (k + 1) F y`
is bounded by the sum over the 3 standard basis vectors `coordinateVector i` of
`‖iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y‖`. -/
theorem norm_iteratedFDeriv_succ_le_sum_dirSpatialJet {F : SpatialField}
    (hF : ContDiff ℝ ∞ F) (k : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ (k + 1) F y‖ ≤
      ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hfderiv : ContDiffAt ℝ ∞ (fderiv ℝ F) y :=
    hF.contDiffAt.fderiv_right UnforcedLeray.Kernels.infty_add_one_le
  have hcomp : ∀ i : Fin 3,
      iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y =
        (ContinuousLinearMap.apply ℝ Space (coordinateVector i)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ k (fderiv ℝ F) y) := by
    intro i
    have hfun : dirSpatialJet F [coordinateVector i] =
        (ContinuousLinearMap.apply ℝ Space (coordinateVector i)) ∘ fderiv ℝ F := rfl
    rw [hfun]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left
      (ContinuousLinearMap.apply ℝ Space (coordinateVector i)) hfderiv
      (by exact_mod_cast le_top)
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun i _ => norm_nonneg _) fun m => ?_
  calc ‖iteratedFDeriv ℝ k (fderiv ℝ F) y m‖
      ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (fderiv ℝ F) y m (coordinateVector i)‖ :=
        FirstOrderPhaseDerivSub.opNorm_le_sum_coordinates (iteratedFDeriv ℝ k (fderiv ℝ F) y m)
    _ = ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y m‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcomp i]
        rfl
    _ ≤ ∑ i : Fin 3,
          ‖iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y‖ * ∏ j : Fin k, ‖m j‖ :=
        Finset.sum_le_sum fun i _ =>
          (iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y).le_opNorm m
    _ = (∑ i : Fin 3, ‖iteratedFDeriv ℝ k (dirSpatialJet F [coordinateVector i]) y‖) *
          ∏ j : Fin k, ‖m j‖ := by
        rw [← Finset.sum_mul]

/-- The `m`-th iterated spatial derivative of a coordinate directional jet
`dirSpatialJet h [coordinateVector i]` is bounded in `L⁴(ℝ³)` by the `(m + 1)`-th iterated spatial
derivative of `h`. -/
theorem eLpNorm_iteratedFDeriv_dirSpatialJet_coord_le {h : SpatialField}
    (hh : ContDiff ℝ ∞ h) (m : ℕ) (i : Fin 3) :
    eLpNorm (fun y => iteratedFDeriv ℝ m (dirSpatialJet h [coordinateVector i]) y) 4 volume ≤
      eLpNorm (fun y => iteratedFDeriv ℝ (m + 1) h y) 4 volume := by
  have hpt : ∀ y : Space,
      ‖iteratedFDeriv ℝ m (dirSpatialJet h [coordinateVector i]) y‖ ≤
        ‖iteratedFDeriv ℝ (m + 1) h y‖ := by
    intro y
    have h1 := JointSmoothSub.norm_iteratedFDeriv_dirSpatialJet_le hh [coordinateVector i] m y
    have h2 : ([coordinateVector i].map norm).prod ≤ 1 := by
      simp only [List.map_singleton, List.prod_singleton]
      exact FirstOrderPhaseDerivSub.norm_coordinateVector_le_one i
    have h3 : ‖iteratedFDeriv ℝ (m + [coordinateVector i].length) h y‖ *
        ([coordinateVector i].map norm).prod ≤
        ‖iteratedFDeriv ℝ (m + 1) h y‖ * 1 := by
      rw [List.length_singleton]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    exact (h1.trans h3).trans ( by rw [mul_one] )
  exact eLpNorm_mono hpt

theorem memLp_iteratedFDeriv_dirSpatialJet_coord {h : SpatialField}
    (hh : ContDiff ℝ ∞ h)
    (hhm : ∀ m : ℕ, MemLp (fun y => iteratedFDeriv ℝ m h y) 4 volume)
    (i : Fin 3) (m : ℕ) :
    MemLp (fun y => iteratedFDeriv ℝ m (dirSpatialJet h [coordinateVector i]) y) 4 volume := by
  have hhi : ContDiff ℝ ∞ (dirSpatialJet h [coordinateVector i]) :=
    JointSmoothSub.contDiff_infty_dirSpatialJet hh [coordinateVector i]
  refine ⟨(hhi.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable, ?_⟩
  exact (eLpNorm_iteratedFDeriv_dirSpatialJet_coord_le hh m i).trans_lt (hhm (m + 1)).eLpNorm_lt_top

/-- By induction on `k : ℕ`, if `IsSmoothLerayRep f g` holds for smooth `f, g : SpatialField` with
all iterated derivatives in `L⁴(ℝ³)`, then for every `k : ℕ`,
`eLpNorm (fun y => iteratedFDeriv ℝ k g y) 4 volume` is bounded by
`(3 : ℝ≥0∞) ^ k * ‖RieszLp.lerayLp 4 _ _‖₊ * eLpNorm (fun y => iteratedFDeriv ℝ k f y) 4 volume`. -/
theorem eLpNorm_iteratedFDeriv_lerayRep_le (k : ℕ) :
    ∀ {f g : SpatialField},
      ContDiff ℝ ∞ f →
      (∀ m : ℕ, MemLp (fun y => iteratedFDeriv ℝ m f y) 4 volume) →
      (∀ m : ℕ, MemLp (fun y => iteratedFDeriv ℝ m g y) 4 volume) →
      IsSmoothLerayRep f g →
      eLpNorm (fun y => iteratedFDeriv ℝ k g y) 4 volume ≤
        (3 : ℝ≥0∞) ^ k *
          ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ *
          eLpNorm (fun y => iteratedFDeriv ℝ k f y) 4 volume := by
  induction k with
  | zero =>
      intro f g _ _ _ hrep
      obtain ⟨hf0, _, heq⟩ := hrep
      have h0g : eLpNorm (fun y => iteratedFDeriv ℝ 0 g y) 4 volume = eLpNorm g 4 volume :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero)
      have h0f : eLpNorm (fun y => iteratedFDeriv ℝ 0 f y) 4 volume = eLpNorm f 4 volume :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero)
      rw [h0g, h0f, pow_zero, one_mul, eLpNorm_congr_ae heq]
      exact UnforcedLeray.RieszLp.eLpNorm_lerayLp_toLp_le 4 (by norm_num) (by norm_num) hf0
  | succ k ih =>
      intro f g hf hfm hgm hrep
      have hg : ContDiff ℝ ∞ g := hrep.2.1
      have hpt : ∀ y : Space,
          ‖iteratedFDeriv ℝ (k + 1) g y‖ ≤
            ‖(∑ i : Fin 3, fun y' =>
              ‖iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y'‖) y‖ := by
        intro y
        rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact norm_iteratedFDeriv_succ_le_sum_dirSpatialJet hg k y
      have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
          AEStronglyMeasurable
            (fun y : Space => ‖iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y‖)
            volume := by
        intro i _
        exact ((JointSmoothSub.contDiff_infty_dirSpatialJet hg
          [coordinateVector i]).continuous_iteratedFDeriv
          (by exact_mod_cast le_top)).norm.aestronglyMeasurable
      have htri :
          eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) g y) 4 volume ≤
            ∑ i : Fin 3,
              eLpNorm (fun y => iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y)
                4 volume := by
        calc eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) g y) 4 volume
            ≤ eLpNorm (∑ i : Fin 3, fun y =>
                ‖iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y‖) 4 volume :=
              eLpNorm_mono hpt
          _ ≤ ∑ i : Fin 3,
                eLpNorm (fun y =>
                  ‖iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y‖) 4 volume :=
              eLpNorm_sum_le hmeas (by norm_num)
          _ = ∑ i : Fin 3,
                eLpNorm (fun y => iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y)
                  4 volume := by
              simp_rw [eLpNorm_norm]
      have hstep : ∀ i : Fin 3,
          eLpNorm (fun y => iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y)
            4 volume ≤
          (3 : ℝ≥0∞) ^ k *
            ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ *
            eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) f y) 4 volume := by
        intro i
        have hrepi : IsSmoothLerayRep (dirSpatialJet f [coordinateVector i])
            (dirSpatialJet g [coordinateVector i]) :=
          isSmoothLerayRep_dirSpatialJet hf hfm hgm hrep [coordinateVector i]
        have h1 := ih
          (JointSmoothSub.contDiff_infty_dirSpatialJet hf [coordinateVector i])
          (memLp_iteratedFDeriv_dirSpatialJet_coord hf hfm i)
          (memLp_iteratedFDeriv_dirSpatialJet_coord hg hgm i)
          hrepi
        have h2 := eLpNorm_iteratedFDeriv_dirSpatialJet_coord_le hf k i
        exact h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
      calc eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) g y) 4 volume
          ≤ ∑ i : Fin 3,
              eLpNorm (fun y => iteratedFDeriv ℝ k (dirSpatialJet g [coordinateVector i]) y)
                4 volume := htri
        _ ≤ ∑ _i : Fin 3,
              (3 : ℝ≥0∞) ^ k *
                ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ *
                eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) f y) 4 volume :=
            Finset.sum_le_sum fun i _ => hstep i
        _ = (3 : ℝ≥0∞) ^ (k + 1) *
              ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ *
              eLpNorm (fun y => iteratedFDeriv ℝ (k + 1) f y) 4 volume := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_ofNat, pow_succ']
            ring

end SmoothLeraySliceSub

/-! ## 5. Atomic analytical leaves and assembly of `SmoothLeraySliceRegularity` -/

/-- **`PartII-b:S3/1/2/1/1` (`SmoothLerayRepExists`)**
(`the November 2 reference manuscript`,
lines 2552 and 2559-2562: "These estimates are uniform in phase; the bounded Cartesian Leray map
preserves them in $W^{k,p}$. ... On positive physical-time compact intervals the resulting
$C_\tau W^{k,4}$ regularity and the projected equation give all time derivatives"):
for every smooth spatial vector field `f : SpatialField` whose iterated spatial derivatives
`iteratedFDeriv ℝ k f` all belong to `L⁴(ℝ³)`, `RieszLp.lerayLp 4 (hf.toLp f)` admits a `C^∞`
representative `g : SpatialField` (`IsSmoothLerayRep f g`) whose iterated spatial derivatives all
belong to `L⁴(ℝ³)`.
Composed by `smoothLeraySliceRegularity_of` in task `PartII-b:S3/1/2/1`. -/
def SmoothLerayRepExists : Prop :=
  ∀ f : SpatialField, ContDiff ℝ ∞ f →
    (∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) →
    ∃ g : SpatialField, IsSmoothLerayRep f g ∧
      ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k g y) 4 volume

/-- **`PartII-b:S3/1/2/1/2` (`SmoothLeraySliceDerivZero`)**
(`the November 2 reference manuscript`,
lines 2552 and 2559-2562: "These estimates are uniform in phase; the bounded Cartesian Leray map
preserves them in $W^{k,p}$. ... On positive physical-time compact intervals the resulting
$C_\tau W^{k,4}$ regularity and the projected equation give all time derivatives"):
given `SmoothLerayRepExists`, if `F, F' : ℝ → SpatialField` lie in `IsUniformSmoothL4SliceFamily`
and `HasPhaseJetDeriv F F'`, then `τ' ↦ smoothLeraySlice F τ' y` has derivative
`smoothLeraySlice F' τ y` at every `(τ, y) ∈ ℝ × Space`.
Composed by `smoothLeraySliceRegularity_of` in task `PartII-b:S3/1/2/1`. -/
def SmoothLeraySliceDerivZero : Prop :=
  SmoothLerayRepExists →
  ∀ F F' : ℝ → SpatialField,
    IsUniformSmoothL4SliceFamily F → IsUniformSmoothL4SliceFamily F' →
    HasPhaseJetDeriv F F' →
    ∀ (τ : ℝ) (y : Space),
      HasDerivAt (fun τ' : ℝ => smoothLeraySlice F τ' y) (smoothLeraySlice F' τ y) τ

namespace SmoothLeraySliceSub

/-- From `SmoothLerayRepExists`, every slice `F τ` of `F ∈ IsUniformSmoothL4SliceFamily` satisfies
`IsSmoothLerayRep (F τ) (smoothLeraySlice F τ)` and has all iterated derivatives of
`smoothLeraySlice F τ` in `L⁴(ℝ³)`. -/
theorem smoothLeraySlice_rep_and_memLp (hRep : SmoothLerayRepExists)
    {F : ℝ → SpatialField} (hF : IsUniformSmoothL4SliceFamily F) (τ : ℝ) :
    IsSmoothLerayRep (F τ) (smoothLeraySlice F τ) ∧
      ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k (smoothLeraySlice F τ) y) 4 volume := by
  obtain ⟨g, hg_rep, hg_m⟩ := hRep (F τ)
    (HigherPhaseSub.sliceFamily_contDiff_infty hF τ)
    (fun k => memLp_iteratedFDeriv_of_sliceFamily hF k τ)
  have heq : smoothLeraySlice F τ = g :=
    HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep hg_rep
  rw [heq]
  exact ⟨hg_rep, hg_m⟩

/-- Linearity of `smoothLeraySlice` on first-order Taylor remainders
`F (τ + h) - F τ - h • F' τ` for `F, F' ∈ IsUniformSmoothL4SliceFamily`. -/
theorem smoothLeraySlice_sub_sub_smul (hRep : SmoothLerayRepExists)
    {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (τ h : ℝ) :
    smoothLeraySlice F (τ + h) - smoothLeraySlice F τ - h • smoothLeraySlice F' τ =
      smoothLerayProj (F (τ + h) - F τ - h • F' τ) := by
  have h1 := (smoothLeraySlice_rep_and_memLp hRep hF (τ + h)).1
  have h2 := (smoothLeraySlice_rep_and_memLp hRep hF τ).1
  have h3 := (smoothLeraySlice_rep_and_memLp hRep hF' τ).1
  have hsub12 : IsSmoothLerayRep (F (τ + h) - F τ)
      (smoothLerayProj (F (τ + h) - F τ)) := by
    rw [smoothLerayProj_sub h1 h2]
    exact isSmoothLerayRep_sub h1 h2
  have hsmul3 : IsSmoothLerayRep (h • F' τ) (smoothLerayProj (h • F' τ)) := by
    rw [smoothLerayProj_smul h h3]
    exact isSmoothLerayRep_smul h h3
  change smoothLerayProj (F (τ + h)) - smoothLerayProj (F τ) -
      h • smoothLerayProj (F' τ) = _
  rw [← smoothLerayProj_sub h1 h2, ← smoothLerayProj_smul h h3,
    ← smoothLerayProj_sub hsub12 hsmul3]

/-- From `SmoothLerayRepExists`, `smoothLeraySlice` commutes with `dirSpatialJet` on
`IsUniformSmoothL4SliceFamily`. -/
theorem smoothLeraySlice_dirSpatialJet (hRep : SmoothLerayRepExists)
    {F : ℝ → SpatialField} (hF : IsUniformSmoothL4SliceFamily F)
    (ws : List Space) (τ : ℝ) :
    smoothLeraySlice (fun τ' => dirSpatialJet (F τ') ws) τ =
      dirSpatialJet (smoothLeraySlice F τ) ws := by
  obtain ⟨hrep, hgm⟩ := smoothLeraySlice_rep_and_memLp hRep hF τ
  exact smoothLerayProj_dirSpatialJet
    (HigherPhaseSub.sliceFamily_contDiff_infty hF τ)
    (fun k => memLp_iteratedFDeriv_of_sliceFamily hF k τ)
    hgm hrep ws

/-- From `SmoothLerayRepExists` and the proved 3D Morrey embedding `smoothMorreyL4FieldBound_proof`,
for every `F ∈ IsUniformSmoothL4SliceFamily`, every slice `F τ` has smooth Leray representative
`smoothLeraySlice F τ` and `smoothLeraySlice F` lies in `IsUniformSmoothL4SliceFamily`. -/
theorem sliceFamily_smoothLeraySlice_of_repExists (hRep : SmoothLerayRepExists)
    (F : ℝ → SpatialField) (hF : IsUniformSmoothL4SliceFamily F) :
    (∀ τ : ℝ, IsSmoothLerayRep (F τ) (smoothLeraySlice F τ)) ∧
      IsUniformSmoothL4SliceFamily (smoothLeraySlice F) := by
  have hslice : ∀ τ : ℝ, IsSmoothLerayRep (F τ) (smoothLeraySlice F τ) ∧
      ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k (smoothLeraySlice F τ) y) 4 volume :=
    smoothLeraySlice_rep_and_memLp hRep hF
  refine ⟨fun τ => (hslice τ).1, ?_⟩
  refine isUniformSmoothL4SliceFamily_of_morreyL4
    (smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof) (smoothLeraySlice F)
    (fun k τ => ((hslice τ).1.2.1).of_le (by exact_mod_cast le_top)) ?_
  intro k
  obtain ⟨M, hM⟩ := hF.l4_bounded k
  set CL : ℝ := (‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ : ℝ)
  have hCL : 0 ≤ CL := NNReal.coe_nonneg _
  refine ⟨(3 : ℝ) ^ k * CL * max M 0, fun τ => ?_⟩
  have hbound := eLpNorm_iteratedFDeriv_lerayRep_le k
    (HigherPhaseSub.sliceFamily_contDiff_infty hF τ)
    (fun m => memLp_iteratedFDeriv_of_sliceFamily hF m τ)
    (hslice τ).2 (hslice τ).1
  have hM' : eLpNorm (fun y => iteratedFDeriv ℝ k (F τ) y) 4 volume ≤
      ENNReal.ofReal (max M 0) :=
    (hM τ).trans (ENNReal.ofReal_le_ofReal (le_max_left M 0))
  have hcoe : ((3 : ℝ≥0∞) ^ k *
      ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊) =
      ENNReal.ofReal ((3 : ℝ) ^ k * CL) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  calc eLpNorm (fun y => iteratedFDeriv ℝ k (smoothLeraySlice F τ) y) 4 volume
      ≤ (3 : ℝ≥0∞) ^ k *
          ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ *
          eLpNorm (fun y => iteratedFDeriv ℝ k (F τ) y) 4 volume := hbound
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ k * CL) * ENNReal.ofReal (max M 0) := by
        rw [← hcoe]
        gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ k * CL * max M 0) :=
        (ENNReal.ofReal_mul (by positivity)).symm

/-- From `SmoothLerayRepExists` and `SmoothLeraySliceDerivZero`, `HasPhaseJetDeriv` is preserved by
`smoothLeraySlice` along all iterated spatial directional jets `ws : List Space`. -/
theorem hasPhaseJetDeriv_smoothLeraySlice_of_zero
    (hRep : SmoothLerayRepExists)
    (hDeriv0 : SmoothLeraySliceDerivZero)
    (F F' : ℝ → SpatialField)
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (dF : HasPhaseJetDeriv F F') :
    HasPhaseJetDeriv (smoothLeraySlice F) (smoothLeraySlice F') := by
  intro ws τ y
  have hF_ws : IsUniformSmoothL4SliceFamily (fun τ' => dirSpatialJet (F τ') ws) :=
    HigherPhaseSub.sliceFamily_dirSpatialJet hF ws
  have hF'_ws : IsUniformSmoothL4SliceFamily (fun τ' => dirSpatialJet (F' τ') ws) :=
    HigherPhaseSub.sliceFamily_dirSpatialJet hF' ws
  have dF_ws : HasPhaseJetDeriv (fun τ' => dirSpatialJet (F τ') ws)
      (fun τ' => dirSpatialJet (F' τ') ws) :=
    HigherPhaseSub.hasPhaseJetDeriv_dirSpatialJet dF ws
  have h0 := hDeriv0 hRep
    (fun τ' => dirSpatialJet (F τ') ws)
    (fun τ' => dirSpatialJet (F' τ') ws)
    hF_ws hF'_ws dF_ws τ y
  have hfun : (fun τ' : ℝ => dirSpatialJet (smoothLeraySlice F τ') ws y) =
      (fun τ' : ℝ => smoothLeraySlice (fun s => dirSpatialJet (F s) ws) τ' y) := by
    funext τ'
    rw [smoothLeraySlice_dirSpatialJet hRep hF ws τ']
  have hval : dirSpatialJet (smoothLeraySlice F' τ) ws y =
      smoothLeraySlice (fun s => dirSpatialJet (F' s) ws) τ y :=
    congrFun (smoothLeraySlice_dirSpatialJet hRep hF' ws τ).symm y
  rw [hfun, hval]
  exact h0

end SmoothLeraySliceSub

/-- Conditional assembly of `SmoothLeraySliceRegularity` (`PartII-b:S3/1/2/1`, SP 2552, 2559-2562)
from `SmoothLerayRepExists` (`PartII-b:S3/1/2/1/1`) and `SmoothLeraySliceDerivZero`
(`PartII-b:S3/1/2/1/2`). -/
theorem smoothLeraySliceRegularity_of
    (hRep : SmoothLerayRepExists)
    (hDeriv0 : SmoothLeraySliceDerivZero) :
    SmoothLeraySliceRegularity :=
  ⟨SmoothLeraySliceSub.sliceFamily_smoothLeraySlice_of_repExists hRep,
    SmoothLeraySliceSub.hasPhaseJetDeriv_smoothLeraySlice_of_zero hRep hDeriv0⟩

/-- Alias of `smoothLeraySliceRegularity_of` for backwards compatibility. -/
theorem smoothLeraySliceRegularity_of_parts
    (hRep : SmoothLerayRepExists)
    (hDeriv0 : SmoothLeraySliceDerivZero) :
    SmoothLeraySliceRegularity :=
  smoothLeraySliceRegularity_of hRep hDeriv0

end UnforcedLeray.Short.IIb

end
