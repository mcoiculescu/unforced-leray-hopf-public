import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_1
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Data.Fin.Tuple.Basic

/-!
# `PartII-b:S3/1/2/1/1` (`SmoothLerayRepExists`, SP 2552, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2552 and 2559-2562:
"These estimates are uniform in phase; the bounded Cartesian Leray map preserves them in $W^{k,p}$.
... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives".

Proves `smoothLerayRepExists_proof : UnforcedLeray.Short.IIb.SmoothLerayRepExists`:
for every smooth `f : SpatialField` (`ContDiff ℝ ∞ f`) whose iterated spatial derivatives all belong
to `L⁴(ℝ³)`, `RieszLp.lerayLp 4 (hf0.toLp f)` admits a `C^∞` representative `g : SpatialField`
(`IsSmoothLerayRep f g`) whose iterated spatial derivatives all belong to `L⁴(ℝ³)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

local instance fact_one_le_four_rep : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace SmoothLerayRepExistsAux

/-- Shrinking bump sequence on `Space = EuclideanSpace ℝ (Fin 3)` with `rOut = (n + 1)⁻¹ → 0`. -/
def shrinkBump3 (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨((n : ℝ) + 2)⁻¹, ((n : ℝ) + 1)⁻¹, by positivity,
    (inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith)⟩

theorem tendsto_shrinkBump3_rOut :
    Tendsto (fun n : ℕ => (shrinkBump3 n).rOut) atTop (𝓝 0) := by
  simpa [shrinkBump3, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- `Sob.iterDD vs u` agrees with `dirSpatialJet u vs`. -/
theorem iterDD_eq_dirSpatialJet (vs : List Space) (u : SpatialField) :
    UnforcedLeray.Sob.iterDD vs u = dirSpatialJet u vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      funext y
      simp [UnforcedLeray.Sob.iterDD_cons, dirSpatialJet, ih]

/-- `L⁴(ℝ³)` Leray projection of the directional spatial jet `dirSpatialJet f ws`. -/
def lerayJet (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (ws : List Space) : SpatialField :=
  (UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)
    ((SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv hf ws
      (hfm ws.length)).toLp (dirSpatialJet f ws)) : SpatialField)

theorem memLp_lerayJet (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (ws : List Space) :
    MemLp (lerayJet f hf hfm ws) 4 volume :=
  Lp.memLp _

theorem locallyIntegrable_lerayJet (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (ws : List Space) :
    LocallyIntegrable (lerayJet f hf hfm ws) volume :=
  (memLp_lerayJet f hf hfm ws).locallyIntegrable (by norm_num)

/-- For every list of coordinate indices `is : List (Fin 3)`, `lerayJet f hf hfm (is.map coordinateVector)`
is the weak derivative of `lerayJet f hf hfm []` along `is.map coordinateVector`. -/
theorem hasWeakDeriv_lerayJet_coordList (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) :
    ∀ is : List (Fin 3),
      UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.wholeSpace 3)
        (is.map coordinateVector)
        (lerayJet f hf hfm [])
        (lerayJet f hf hfm (is.map coordinateVector))
  | [] =>
      UnforcedLeray.Sob.HasWeakDeriv.nil fun φ hφ =>
        (locallyIntegrable_lerayJet f hf hfm []).integrable_smul_left_of_hasCompactSupport
          hφ.1.continuous hφ.2
  | i :: is => by
      have ih := hasWeakDeriv_lerayJet_coordList f hf hfm is
      have hstep : HasWeakSpatialDerivative i
          (lerayJet f hf hfm (is.map coordinateVector))
          (lerayJet f hf hfm (coordinateVector i :: is.map coordinateVector)) :=
        UnforcedLeray.RieszLp.lerayLp_toLp_hasWeakSpatialDerivative
          (by norm_num) (by norm_num)
          (SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv hf
            (is.map coordinateVector) (hfm (is.map coordinateVector).length))
          (SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv hf
            (coordinateVector i :: is.map coordinateVector)
            (hfm (coordinateVector i :: is.map coordinateVector).length))
          (SmoothLeraySliceSub.hasWeakSpatialDerivative_dirSpatialJet hf
            (is.map coordinateVector) i)
      exact ih.cons (UnforcedLeray.Sob.hasWeakSpatialDerivative_iff.1 hstep)

/-- Mollifying `lerayJet f hf hfm []` commutes with all coordinate directional jets. -/
theorem dirSpatialJet_moll_lerayJet (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (b : ContDiffBump (0 : Space)) (is : List (Fin 3)) :
    dirSpatialJet (UnforcedLeray.Sob.moll b volume (lerayJet f hf hfm []))
      (is.map coordinateVector) =
      UnforcedLeray.Sob.moll b volume
        (lerayJet f hf hfm (is.map coordinateVector)) := by
  rw [← iterDD_eq_dirSpatialJet]
  exact UnforcedLeray.Sob.iterDD_cv_of_hasWeakDeriv (dir := UnforcedLeray.Sob.e)
    (hasWeakDeriv_lerayJet_coordList f hf hfm is)
    (b.contDiff_normed (μ := volume)) (b.hasCompactSupport_normed (μ := volume))
    (locallyIntegrable_lerayJet f hf hfm [])

/-- Coordinate index list associated with a tuple `w : Fin k → Fin 3`. -/
def coordList : ∀ {k : ℕ}, (Fin k → Fin 3) → List (Fin 3)
  | 0, _ => []
  | _ + 1, w => coordList (Fin.tail w) ++ [w 0]

/-- Pointwise bound on `iteratedFDeriv ℝ k H y` by the sum over all coordinate words of length `k`. -/
theorem norm_iteratedFDeriv_le_sum_coordList :
    ∀ (k : ℕ) {H : SpatialField}, ContDiff ℝ ∞ H → ∀ y : Space,
      ‖iteratedFDeriv ℝ k H y‖ ≤
        ∑ w : Fin k → Fin 3, ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖
  | 0, H, _, y => by
      rw [Fintype.sum_unique]
      simp [coordList, norm_iteratedFDeriv_zero]
  | k + 1, H, hH, y => by
      calc ‖iteratedFDeriv ℝ (k + 1) H y‖
          ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (dirSpatialJet H [coordinateVector i]) y‖ :=
            SmoothLeraySliceSub.norm_iteratedFDeriv_succ_le_sum_dirSpatialJet hH k y
        _ ≤ ∑ i : Fin 3, ∑ w' : Fin k → Fin 3,
              ‖dirSpatialJet (dirSpatialJet H [coordinateVector i])
                ((coordList w').map coordinateVector) y‖ :=
            Finset.sum_le_sum fun i _ =>
              norm_iteratedFDeriv_le_sum_coordList k
                (JointSmoothSub.contDiff_infty_dirSpatialJet hH [coordinateVector i]) y
        _ = ∑ p : Fin 3 × (Fin k → Fin 3),
              ‖dirSpatialJet H ((coordList (Fin.cons p.1 p.2)).map coordinateVector) y‖ := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w' _ => ?_
            simp [coordList, HigherPhaseSub.dirSpatialJet_append]
        _ = ∑ w : Fin (k + 1) → Fin 3,
              ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖ :=
            Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 3))
              (fun w => ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖)

/-- `L⁴(ℝ³)` norm bound on `iteratedFDeriv ℝ k H` by the sum over all coordinate words of length `k`. -/
theorem eLpNorm_iteratedFDeriv_le_sum_coordList (k : ℕ) {H : SpatialField}
    (hH : ContDiff ℝ ∞ H) :
    eLpNorm (fun y => iteratedFDeriv ℝ k H y) 4 volume ≤
      ∑ w : Fin k → Fin 3,
        eLpNorm (dirSpatialJet H ((coordList w).map coordinateVector)) 4 volume := by
  have hpt : ∀ y : Space,
      ‖iteratedFDeriv ℝ k H y‖ ≤
        ‖(∑ w : Fin k → Fin 3, fun y' =>
          ‖dirSpatialJet H ((coordList w).map coordinateVector) y'‖) y‖ := by
    intro y
    rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact norm_iteratedFDeriv_le_sum_coordList k hH y
  have hmeas : ∀ w ∈ (Finset.univ : Finset (Fin k → Fin 3)),
      AEStronglyMeasurable
        (fun y : Space => ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖) volume := by
    intro w _
    exact (JointSmoothSub.contDiff_infty_dirSpatialJet hH
      ((coordList w).map coordinateVector)).continuous.norm.aestronglyMeasurable
  calc eLpNorm (fun y => iteratedFDeriv ℝ k H y) 4 volume
      ≤ eLpNorm (∑ w : Fin k → Fin 3, fun y =>
          ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖) 4 volume :=
        eLpNorm_mono hpt
    _ ≤ ∑ w : Fin k → Fin 3,
          eLpNorm (fun y =>
            ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖) 4 volume :=
        eLpNorm_sum_le hmeas (by norm_num)
    _ = ∑ w : Fin k → Fin 3,
          eLpNorm (dirSpatialJet H ((coordList w).map coordinateVector)) 4 volume := by
        simp_rw [eLpNorm_norm]

/-- Mollified sequence `g_n = moll (shrinkBump3 n) (lerayJet f hf hfm [])`. -/
def mollSeq (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (n : ℕ) : SpatialField :=
  UnforcedLeray.Sob.moll (shrinkBump3 n) volume (lerayJet f hf hfm [] : SpatialField)

theorem contDiff_mollSeq (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollSeq f hf hfm n) :=
  UnforcedLeray.Sob.contDiff_moll (shrinkBump3 n) (locallyIntegrable_lerayJet f hf hfm [])

/-- Sum of `L⁴` mollification errors over all coordinate words of length `k`. -/
def mollErr (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (k n : ℕ) : ℝ≥0∞ :=
  ∑ w : Fin k → Fin 3,
    eLpNorm ((lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField) -
      UnforcedLeray.Sob.moll (shrinkBump3 n) volume
        (lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField)) 4 volume

theorem mollErr_lt_top (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (k n : ℕ) :
    mollErr f hf hfm k n < ⊤ := by
  refine ENNReal.sum_lt_top.2 fun w _ => ?_
  set u : SpatialField := lerayJet f hf hfm ((coordList w).map coordinateVector)
  have hu : MemLp u 4 volume := memLp_lerayJet f hf hfm ((coordList w).map coordinateVector)
  have hmoll : MemLp (UnforcedLeray.Sob.moll (shrinkBump3 n) volume u) 4 volume :=
    UnforcedLeray.Sob.memLp_moll (shrinkBump3 n) (by norm_num) (by norm_num) hu
      (UnforcedLeray.Sob.contDiff_moll (shrinkBump3 n)
        (hu.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable
  exact (hu.sub hmoll).eLpNorm_lt_top

theorem tendsto_mollErr (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) (k : ℕ) :
    Tendsto (fun n : ℕ => mollErr f hf hfm k n) atTop (𝓝 0) := by
  have hterm : ∀ w ∈ (Finset.univ : Finset (Fin k → Fin 3)),
      Tendsto (fun n : ℕ =>
        eLpNorm (lerayJet f hf hfm ((coordList w).map coordinateVector) -
          UnforcedLeray.Sob.moll (shrinkBump3 n) volume
            (lerayJet f hf hfm ((coordList w).map coordinateVector))) 4 volume)
        atTop (𝓝 0) := fun w _ =>
    UnforcedLeray.Sob.tendsto_eLpNorm_moll_sub (by norm_num)
      (memLp_lerayJet f hf hfm ((coordList w).map coordinateVector))
      tendsto_shrinkBump3_rOut
  simpa [mollErr] using tendsto_finsetSum Finset.univ hterm

theorem tendsto_mollErr_toReal (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) (k : ℕ) :
    Tendsto (fun n : ℕ => (mollErr f hf hfm k n).toReal) atTop (𝓝 0) := by
  rw [← ENNReal.toReal_zero]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_mollErr f hf hfm k)

theorem eLpNorm_iteratedFDeriv_mollSeq_sub_le (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume)
    (k m n : ℕ) :
    eLpNorm (fun y => iteratedFDeriv ℝ k (mollSeq f hf hfm m - mollSeq f hf hfm n) y) 4 volume ≤
      ENNReal.ofReal ((mollErr f hf hfm k m).toReal + (mollErr f hf hfm k n).toReal) := by
  have hdiff : ContDiff ℝ ∞ (mollSeq f hf hfm m - mollSeq f hf hfm n) :=
    (contDiff_mollSeq f hf hfm m).sub (contDiff_mollSeq f hf hfm n)
  have h1 := eLpNorm_iteratedFDeriv_le_sum_coordList k hdiff
  have hstep : ∀ w : Fin k → Fin 3,
      eLpNorm (dirSpatialJet (mollSeq f hf hfm m - mollSeq f hf hfm n)
        ((coordList w).map coordinateVector)) 4 volume ≤
      eLpNorm ((lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField) -
        UnforcedLeray.Sob.moll (shrinkBump3 m) volume
          (lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField)) 4 volume +
      eLpNorm ((lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField) -
        UnforcedLeray.Sob.moll (shrinkBump3 n) volume
          (lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField)) 4 volume := by
    intro w
    set ws := (coordList w).map coordinateVector
    set u : SpatialField := lerayJet f hf hfm ws
    have hu : MemLp u 4 volume := memLp_lerayJet f hf hfm ws
    have hjet : dirSpatialJet (mollSeq f hf hfm m - mollSeq f hf hfm n) ws =
        UnforcedLeray.Sob.moll (shrinkBump3 m) volume u -
          UnforcedLeray.Sob.moll (shrinkBump3 n) volume u := by
      rw [HigherPhaseSub.dirSpatialJet_sub (contDiff_mollSeq f hf hfm m)
        (contDiff_mollSeq f hf hfm n) ws]
      dsimp [mollSeq]
      rw [dirSpatialJet_moll_lerayJet f hf hfm (shrinkBump3 m) (coordList w),
        dirSpatialJet_moll_lerayJet f hf hfm (shrinkBump3 n) (coordList w)]
    rw [hjet]
    have hdecomp : UnforcedLeray.Sob.moll (shrinkBump3 m) volume u -
        UnforcedLeray.Sob.moll (shrinkBump3 n) volume u =
        (u - UnforcedLeray.Sob.moll (shrinkBump3 n) volume u) -
          (u - UnforcedLeray.Sob.moll (shrinkBump3 m) volume u) := by
      abel
    rw [hdecomp]
    have hm_meas : AEStronglyMeasurable
        (u - UnforcedLeray.Sob.moll (shrinkBump3 m) volume u) volume :=
      hu.1.sub (UnforcedLeray.Sob.contDiff_moll (shrinkBump3 m)
        (hu.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable
    have hn_meas : AEStronglyMeasurable
        (u - UnforcedLeray.Sob.moll (shrinkBump3 n) volume u) volume :=
      hu.1.sub (UnforcedLeray.Sob.contDiff_moll (shrinkBump3 n)
        (hu.locallyIntegrable (by norm_num))).continuous.aestronglyMeasurable
    calc eLpNorm ((u - UnforcedLeray.Sob.moll (shrinkBump3 n) volume u) -
            (u - UnforcedLeray.Sob.moll (shrinkBump3 m) volume u)) 4 volume
        ≤ eLpNorm (u - UnforcedLeray.Sob.moll (shrinkBump3 n) volume u) 4 volume +
          eLpNorm (u - UnforcedLeray.Sob.moll (shrinkBump3 m) volume u) 4 volume :=
          eLpNorm_sub_le hn_meas hm_meas (by norm_num)
      _ = eLpNorm (u - UnforcedLeray.Sob.moll (shrinkBump3 m) volume u) 4 volume +
          eLpNorm (u - UnforcedLeray.Sob.moll (shrinkBump3 n) volume u) 4 volume :=
          add_comm _ _
  have hsum : eLpNorm (fun y => iteratedFDeriv ℝ k (mollSeq f hf hfm m - mollSeq f hf hfm n) y)
      4 volume ≤ mollErr f hf hfm k m + mollErr f hf hfm k n := by
    refine h1.trans ?_
    rw [mollErr, mollErr, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun w _ => hstep w
  have hcoe : mollErr f hf hfm k m + mollErr f hf hfm k n =
      ENNReal.ofReal ((mollErr f hf hfm k m).toReal + (mollErr f hf hfm k n).toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (mollErr_lt_top f hf hfm k m).ne,
      ENNReal.ofReal_toReal (mollErr_lt_top f hf hfm k n).ne]
  rwa [← hcoe]

/-- Uniformly bounded `L⁴` norm of `iteratedFDeriv ℝ k (mollSeq f hf hfm n)` across `n : ℕ`. -/
theorem eLpNorm_iteratedFDeriv_mollSeq_le (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) (k n : ℕ) :
    eLpNorm (fun y => iteratedFDeriv ℝ k (mollSeq f hf hfm n) y) 4 volume ≤
      ∑ w : Fin k → Fin 3,
        eLpNorm (lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField)
          4 volume := by
  refine (eLpNorm_iteratedFDeriv_le_sum_coordList k (contDiff_mollSeq f hf hfm n)).trans ?_
  refine Finset.sum_le_sum fun w _ => ?_
  dsimp [mollSeq]
  rw [dirSpatialJet_moll_lerayJet f hf hfm (shrinkBump3 n) (coordList w)]
  exact UnforcedLeray.Sob.eLpNorm_moll_le (shrinkBump3 n)
    (memLp_lerayJet f hf hfm ((coordList w).map coordinateVector)).1
    (by norm_num) (by norm_num)

/-- Any sequence of functions `F : ℕ → Space → E` satisfying `‖F m y - F n y‖ ≤ B m + B n`
with `B n → 0` converges uniformly on `Space`. -/
theorem exists_tendstoUniformly_of_norm_sub_le {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ → Space → E) (B : ℕ → ℝ)
    (hB : Tendsto B atTop (𝓝 0))
    (hsub : ∀ (m n : ℕ) (y : Space), ‖F m y - F n y‖ ≤ B m + B n) :
    ∃ G : Space → E, TendstoUniformly F G atTop ∧
      ∀ y : Space, Tendsto (fun n : ℕ => F n y) atTop (𝓝 (G y)) := by
  have hunif : UniformCauchySeqOn F atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop, B n < ε / 2 := hB.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun m hm n hn y _ => ?_⟩
    rw [dist_eq_norm]
    calc ‖F m y - F n y‖
        ≤ B m + B n := hsub m n y
      _ < ε / 2 + ε / 2 := add_lt_add (hN m hm) (hN n hn)
      _ = ε := add_halves ε
  have hpt : ∀ y : Space, ∃ l : E, Tendsto (fun n : ℕ => F n y) atTop (𝓝 l) := by
    intro y
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.1 hunif) ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn y (Set.mem_univ y)⟩
  choose G hG using hpt
  have htu : TendstoUniformlyOn F G atTop Set.univ :=
    hunif.tendstoUniformlyOn_of_tendsto fun y _ => hG y
  exact ⟨G, tendstoUniformlyOn_univ.1 htu, hG⟩

/-- For each `k : ℕ`, `iteratedFDeriv ℝ k (mollSeq f hf hfm n)` converges uniformly on `Space`. -/
theorem exists_tendstoUniformly_iteratedFDeriv_mollSeq (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hfm : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k f y) 4 volume) (k : ℕ) :
    ∃ G : Space → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) Space,
      TendstoUniformly (fun n y => iteratedFDeriv ℝ k (mollSeq f hf hfm n) y) G atTop ∧
      ∀ y : Space, Tendsto (fun n : ℕ => iteratedFDeriv ℝ k (mollSeq f hf hfm n) y)
        atTop (𝓝 (G y)) := by
  obtain ⟨C, hC0, hC⟩ := smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof k
  set B : ℕ → ℝ := fun n =>
    C * ((mollErr f hf hfm k n).toReal + (mollErr f hf hfm (k + 1) n).toReal)
  have hB : Tendsto B atTop (𝓝 0) := by
    have hsum := (tendsto_mollErr_toReal f hf hfm k).add
      (tendsto_mollErr_toReal f hf hfm (k + 1))
    simpa [B] using hsum.const_mul C
  refine exists_tendstoUniformly_of_norm_sub_le
    (fun n y => iteratedFDeriv ℝ k (mollSeq f hf hfm n) y) B hB ?_
  intro m n y
  have hdiff : ContDiff ℝ ∞ (mollSeq f hf hfm m - mollSeq f hf hfm n) :=
    (contDiff_mollSeq f hf hfm m).sub (contDiff_mollSeq f hf hfm n)
  have hsub_eq : iteratedFDeriv ℝ k (mollSeq f hf hfm m) y -
      iteratedFDeriv ℝ k (mollSeq f hf hfm n) y =
      iteratedFDeriv ℝ k (mollSeq f hf hfm m - mollSeq f hf hfm n) y := by
    exact (iteratedFDeriv_sub_apply
      ((contDiff_mollSeq f hf hfm m).contDiffAt.of_le (by exact_mod_cast le_top))
      ((contDiff_mollSeq f hf hfm n).contDiffAt.of_le (by exact_mod_cast le_top))).symm
  rw [hsub_eq]
  set M₀ : ℝ := (mollErr f hf hfm k m).toReal + (mollErr f hf hfm k n).toReal
  set M₁ : ℝ := (mollErr f hf hfm (k + 1) m).toReal + (mollErr f hf hfm (k + 1) n).toReal
  have hM₀ : 0 ≤ M₀ := by positivity
  have hM₁ : 0 ≤ M₁ := by positivity
  have hmorrey := hC (mollSeq f hf hfm m - mollSeq f hf hfm n) hdiff M₀ M₁
    (eLpNorm_iteratedFDeriv_mollSeq_sub_le f hf hfm k m n)
    (eLpNorm_iteratedFDeriv_mollSeq_sub_le f hf hfm (k + 1) m n) y
  rw [max_eq_left hM₀, max_eq_left hM₁] at hmorrey
  calc ‖iteratedFDeriv ℝ k (mollSeq f hf hfm m - mollSeq f hf hfm n) y‖
      ≤ C * (M₀ + M₁) := hmorrey
    _ = B m + B n := by dsimp [B, M₀, M₁]; ring

end SmoothLerayRepExistsAux

/-- **`PartII-b:S3/1/2/1/1` (`SmoothLerayRepExists`)**
(`the November 2 reference manuscript`,
lines 2552 and 2559-2562: "These estimates are uniform in phase; the bounded Cartesian Leray map
preserves them in $W^{k,p}$. ... On positive physical-time compact intervals the resulting
$C_\tau W^{k,4}$ regularity and the projected equation give all time derivatives"):
for every smooth `f : SpatialField` whose iterated spatial derivatives all belong to `L⁴(ℝ³)`,
`RieszLp.lerayLp 4 (hf0.toLp f)` admits a `C^∞` representative `g : SpatialField`
(`IsSmoothLerayRep f g`) whose iterated spatial derivatives all belong to `L⁴(ℝ³)`. -/
theorem smoothLerayRepExists_proof : UnforcedLeray.Short.IIb.SmoothLerayRepExists := by
  intro f hf hfm
  open SmoothLerayRepExistsAux in
  choose G hG_unif hG_pt using exists_tendstoUniformly_iteratedFDeriv_mollSeq f hf hfm
  let I₀ := continuousMultilinearCurryFin0 ℝ Space Space
  let g : SpatialField := fun y => I₀ (G 0 y)
  have hg_pt : ∀ y : Space, Tendsto (fun n : ℕ => mollSeq f hf hfm n y) atTop (𝓝 (g y)) := by
    intro y
    have h0 := (I₀.continuous.tendsto (G 0 y)).comp (hG_pt 0 y)
    refine h0.congr fun n => ?_
    simp [I₀, iteratedFDeriv_zero_eq_comp]
  have hG_fderiv : ∀ (k : ℕ) (y : Space),
      HasFDerivAt (G k)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) Space
          (G (k + 1) y)) y := by
    intro k y
    let Ik := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) Space
    have hunif_k : TendstoUniformly
        (fun n y' => Ik (iteratedFDeriv ℝ (k + 1) (mollSeq f hf hfm n) y'))
        (fun y' => Ik (G (k + 1) y')) atTop :=
      Ik.isometry.uniformContinuous.comp_tendstoUniformly (hG_unif (k + 1))
    have hderiv_n : ∀ (n : ℕ) (y' : Space),
        HasFDerivAt (iteratedFDeriv ℝ k (mollSeq f hf hfm n))
          (Ik (iteratedFDeriv ℝ (k + 1) (mollSeq f hf hfm n) y')) y' := by
      intro n y'
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k (mollSeq f hf hfm n)) y' :=
        ((contDiff_mollSeq f hf hfm n).differentiable_iteratedFDeriv
          (by exact_mod_cast WithTop.coe_lt_top k)) y'
      have heq : Ik (iteratedFDeriv ℝ (k + 1) (mollSeq f hf hfm n) y') =
          fderiv ℝ (iteratedFDeriv ℝ k (mollSeq f hf hfm n)) y' := by
        rw [iteratedFDeriv_succ_eq_comp_left]
        simp [Ik]
      rw [heq]
      exact hdiff.hasFDerivAt
    exact hasFDerivAt_of_tendstoUniformly hunif_k hderiv_n (hG_pt k) y
  have hiter_eq : ∀ k : ℕ, iteratedFDeriv ℝ k g = G k := by
    intro k
    induction k with
    | zero =>
        funext y
        simp [g, I₀, iteratedFDeriv_zero_eq_comp]
    | succ k ih =>
        funext y
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih,
          (hG_fderiv k y).fderiv]
        exact (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) => Space) Space).symm_apply_apply (G (k + 1) y)
  have hg_smooth : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_continuous_differentiable]
    refine ⟨fun m _ => ?_, fun m _ => ?_⟩
    · rw [hiter_eq m]
      exact Differentiable.continuous fun y => (hG_fderiv m y).differentiableAt
    · rw [hiter_eq m]
      exact fun y => (hG_fderiv m y).differentiableAt
  have hf0 : MemLp f 4 volume :=
    SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv hf [] (hfm 0)
  have hg_ae : g =ᵐ[volume]
      (UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num) (hf0.toLp f) : SpatialField) := by
    set u0 : SpatialField := lerayJet f hf hfm []
    have hmeas_sub : ∀ n : ℕ, AEStronglyMeasurable (u0 - mollSeq f hf hfm n) volume := fun n =>
      (memLp_lerayJet f hf hfm []).1.sub
        (contDiff_mollSeq f hf hfm n).continuous.aestronglyMeasurable
    have hpt_sub : ∀ᵐ y : Space ∂volume,
        Tendsto (fun n : ℕ => (u0 - mollSeq f hf hfm n) y) atTop (𝓝 ((u0 - g) y)) :=
      Eventually.of_forall fun y => tendsto_const_nhds.sub (hg_pt y)
    have hlim_sub : Tendsto (fun n : ℕ => eLpNorm (u0 - mollSeq f hf hfm n) 4 volume)
        atTop (𝓝 0) :=
      UnforcedLeray.Sob.tendsto_eLpNorm_moll_sub (by norm_num)
        (memLp_lerayJet f hf hfm []) tendsto_shrinkBump3_rOut
    have hle0 : eLpNorm (u0 - g) 4 volume ≤ 0 := by
      calc eLpNorm (u0 - g) 4 volume
          ≤ atTop.liminf (fun n : ℕ => eLpNorm (u0 - mollSeq f hf hfm n) 4 volume) :=
            Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas_sub (u0 - g) hpt_sub
        _ = 0 := hlim_sub.liminf_eq
    have heq0 : u0 - g =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff ((memLp_lerayJet f hf hfm []).1.sub
        hg_smooth.continuous.aestronglyMeasurable) (by norm_num)).1 (le_antisymm hle0 zero_le)
    filter_upwards [heq0] with y hy
    exact (sub_eq_zero.1 hy).symm
  have hg_memLp : ∀ k : ℕ, MemLp (fun y => iteratedFDeriv ℝ k g y) 4 volume := by
    intro k
    refine ⟨(hg_smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable,
      ?_⟩
    set Ck : ℝ≥0∞ :=
      ∑ w : Fin k → Fin 3,
        eLpNorm (lerayJet f hf hfm ((coordList w).map coordinateVector) : SpatialField) 4 volume
    have hCk : Ck < ⊤ :=
      ENNReal.sum_lt_top.2 fun w _ =>
        (memLp_lerayJet f hf hfm ((coordList w).map coordinateVector)).eLpNorm_lt_top
    have hle : eLpNorm (fun y => iteratedFDeriv ℝ k g y) 4 volume ≤ Ck := by
      refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
        (Eventually.of_forall fun n => eLpNorm_iteratedFDeriv_mollSeq_le f hf hfm k n)
        (fun n => ((contDiff_mollSeq f hf hfm n).continuous_iteratedFDeriv
          (by exact_mod_cast le_top)).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [hiter_eq k]
      exact hG_pt k y
    exact hle.trans_lt hCk
  exact ⟨g, ⟨hf0, hg_smooth, hg_ae⟩, hg_memLp⟩

end UnforcedLeray.Short.IIb

end
