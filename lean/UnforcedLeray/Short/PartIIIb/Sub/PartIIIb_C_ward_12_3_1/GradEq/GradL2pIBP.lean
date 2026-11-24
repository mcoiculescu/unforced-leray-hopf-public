import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Short.PartIIa.Tasks.F11SupEmbedding
import UnforcedLeray.Cons.L2.BackgroundConcrete.Spaces
import UnforcedLeray.Units.B0412

/-!
# `GEGradL2p` from the phase-space integration-by-parts inequality (source 2531, 1515-1531)

Task `PartIII-b:C/ward/12/3/1/2/3/org`.  Source of record
`the November 2 reference manuscript`.

`‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}` (2531) is the pure phase-space statement `GradL2pIBP`
(integration by parts of `|Dw|^{2p-2}Dw·Dw`, with `w ∈ L^∞` from the supremum embedding
1515-1531 and `D²w ∈ Y_p`).  Its proof is split into

* `GradL2pMollify` (spatial mollification: smooth bounded approximants of `(w, ∂_jw, ∂_j²w)`
  converging in `L^{q₀}` of the phase measure, with `HasPhaseOp` turned into pointwise
  derivative identities),
* `GradL2pSlice` (the classical slice inequality
  `∫|g|^{2p} ≤ (2p-1) M ∫|g|^{2p-2}|∂g|` for smooth bounded `w`, `g = ∂_jw`, by a spatial cutoff),
* `GradL2pAssemble` (integrate over the period, Hölder, Fatou in the mollification limit).

This file proves `gradL2p_of_hess : GEHess → GradL2pIBP → GEGradL2p`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ENNReal ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params rep)

/-- The phase measure `dτ dy` on `(0, P] × ℝ³`. -/
abbrev phaseμ (P : ℝ) : Measure (ℝ × UnforcedLeray.Space) :=
  (volume.restrict (Ioc (0 : ℝ) P)).prod volume

/-- **The phase-space inequality of source 2531.**  If `w ∈ Y_{q₀}` has a.e. bounded
representative `|w| ≤ M`, `g_j = ∂_jw` and `h_{jk} = ∂_kg_j` are in `Y_{q₀}` (distributionally on
phase tests), then `D_jw ∈ L^{2q₀}` of the phase measure and
`‖D_jw‖²_{2q₀} ≤ (2q₀-1) M ∑_k ‖∂_kD_jw‖_{q₀}`. -/
def GradL2pIBP : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E)
    (g : Fin 3 → Yq P UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq P UnforcedLeray.B0412.q0E) (M : ℝ), 0 ≤ M →
    (∀ᵐ x ∂(phaseμ P), ‖rep w x.1 x.2‖ ≤ M) →
    (∀ j, HasPhaseOp (fun Φ => -dy j Φ) w (g j)) →
    (∀ j k, HasPhaseOp (fun Φ => -dy k Φ) (g j) (h j k)) →
    ∀ j, MemLp (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
        (2 * UnforcedLeray.B0412.q0E) (phaseμ P) ∧
      eLpNorm (fun x : ℝ × UnforcedLeray.Space => rep (g j) x.1 x.2)
          (2 * UnforcedLeray.B0412.q0E) (phaseμ P) ^ 2 ≤
        ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
          ∑ k, eLpNorm (fun x : ℝ × UnforcedLeray.Space => rep (h j k) x.1 x.2)
            UnforcedLeray.B0412.q0E (phaseμ P)

/-- A smooth bounded spatial triple: `w` smooth with `|w| ≤ M`, `g = ∂_jw` smooth and bounded,
`h = ∂_jg`. -/
structure SmoothSlice (M : ℝ) (j : Fin 3) (w g h : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) :
    Prop where
  w_smooth : ContDiff ℝ ∞ w
  g_smooth : ContDiff ℝ ∞ g
  w_le : ∀ y, ‖w y‖ ≤ M
  g_bdd : ∃ K : ℝ, ∀ y, ‖g y‖ ≤ K
  g_eq : ∀ y, fderiv ℝ w y (EuclideanSpace.single j 1) = g y
  h_eq : ∀ y, fderiv ℝ g y (EuclideanSpace.single j 1) = h y

/-- **Slice inequality** (source 2531, classical): for a smooth bounded triple with `g, h ∈ L^{q₀}`
(spatial Lebesgue measure), `∫|g|^{2q₀} ≤ (2q₀-1) M ∫|g|^{2q₀-2}|h|`
(integration by parts of `|g|^{2q₀-2}ḡ·∂_jw` against a spatial cutoff; `t ↦ |t|^{2q₀-2}t̄` is `C¹`
since `2q₀-2 = 7/2 > 1`). -/
def GradL2pSlice : Prop :=
  ∀ (M : ℝ) (j : Fin 3) (w g h : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    0 ≤ M → SmoothSlice M j w g h →
    MemLp g UnforcedLeray.B0412.q0E volume → MemLp h UnforcedLeray.B0412.q0E volume →
    ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal)) ≤
      ENNReal.ofReal ((2 * UnforcedLeray.B0412.q0E.toReal - 1) * M) *
        ∫⁻ y, ENNReal.ofReal
          (‖g y‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖h y‖)

/-- **Mollification** (source 2531 with 1415-1424): spatial mollification of `(w, g_j, h_{jj})`
gives, for each `n`, jointly measurable functions `W n, G n, H n` on `ℝ × ℝ³`, smooth bounded
slices with `|W n| ≤ M`, `G n τ` and `H n τ` in `L^{q₀}(ℝ³)` for every `τ`, `G n` bounded uniformly
in `(τ, y)`, with `G n → rep g_j`, `H n → rep h_{jj}` in `L^{q₀}` of the phase measure. -/
def GradL2pMollify : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (w g h : Yq P UnforcedLeray.B0412.q0E) (M : ℝ) (j : Fin 3), 0 ≤ M →
    (∀ᵐ x ∂(phaseμ P), ‖rep w x.1 x.2‖ ≤ M) →
    HasPhaseOp (fun Φ => -dy j Φ) w g → HasPhaseOp (fun Φ => -dy j Φ) g h →
    ∃ (W G H : ℕ → ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
      (∀ n τ, SmoothSlice M j (fun y => W n (τ, y)) (fun y => G n (τ, y)) (fun y => H n (τ, y))) ∧
      (∀ n τ, MemLp (fun y => G n (τ, y)) UnforcedLeray.B0412.q0E volume ∧
        MemLp (fun y => H n (τ, y)) UnforcedLeray.B0412.q0E volume) ∧
      (∀ n, ∃ K : ℝ, ∀ x, ‖G n x‖ ≤ K) ∧
      (∀ n, AEStronglyMeasurable (G n) (phaseμ P) ∧ AEStronglyMeasurable (H n) (phaseμ P)) ∧
      Filter.Tendsto (fun n => eLpNorm (fun x => G n x - rep g x.1 x.2)
        UnforcedLeray.B0412.q0E (phaseμ P)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => eLpNorm (fun x => H n x - rep h x.1 x.2)
        UnforcedLeray.B0412.q0E (phaseμ P)) Filter.atTop (nhds 0)

/-- **Assembly**: integrate the slice inequality over the period, Hölder with exponents
`(2q₀)/(2q₀-2)` and `q₀`, Fatou in the mollification limit. -/
def GradL2pAssemble : Prop := GradL2pMollify → GradL2pSlice → GradL2pIBP

/-! ### A.e. boundedness of the correction from the supremum embedding -/

/-- A continuous bounded function equal slice-wise a.e. to an `Yq` element bounds its joint
representative a.e. on the phase measure. -/
theorem rep_ae_bound {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (w : Yq P r)
    (W : AddCircle P × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (B : ℝ)
    (hW : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      (fun y => W (τ, y)) =ᵐ[volume] ((w τ : Lp UnforcedLeray.PhaseSpace.CVec3 r
        (volume : Measure UnforcedLeray.Space)) : UnforcedLeray.Space → _))
    (hb : ∀ τ y, ‖W (τ, y)‖ ≤ B) :
    ∀ᵐ x ∂(phaseμ P), ‖rep w x.1 x.2‖ ≤ B := by
  have hmeas : MeasurableSet {x : ℝ × UnforcedLeray.Space | ‖rep w x.1 x.2‖ ≤ B} :=
    measurableSet_le (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep w).measurable.norm
      measurable_const
  unfold phaseμ
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  have hvol : ∀ᵐ τ ∂(volume : Measure (AddCircle P)),
      (fun y => W (τ, y)) =ᵐ[volume] ((w τ : Lp UnforcedLeray.PhaseSpace.CVec3 r
        (volume : Measure UnforcedLeray.Space)) : UnforcedLeray.Space → _) := by
    have hac : (volume : Measure (AddCircle P)) ≪ AddCircle.haarAddCircle (T := P) := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      exact Measure.smul_absolutelyContinuous
    exact hac.ae_le hW
  have hmp := AddCircle.measurePreserving_mk P 0
  have h2 : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)), (fun y => W ((t : AddCircle P), y)) =ᵐ[volume]
      ((w (t : AddCircle P) : Lp UnforcedLeray.PhaseSpace.CVec3 r
        (volume : Measure UnforcedLeray.Space)) : UnforcedLeray.Space → _) := by
    have := hmp.quasiMeasurePreserving.ae hvol
    simpa using this
  filter_upwards [h2] with t ht
  have hs := UnforcedLeray.Cons.C03.Concrete.rep_slice w t
  filter_upwards [hs, ht] with y hy1 hy2
  show ‖rep w t y‖ ≤ B
  rw [hy1, ← hy2]
  exact hb _ _

/-- Regime statement: the correction `w = wOf z` has an a.e. bounded joint representative
(supremum embedding `bg:supremum-embedding`, source 1515-1531, with `P ≤ 1`). -/
theorem geSupBound : GERegime fun p z _ =>
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ M := by
  intro lam q hq dm dp hdm
  refine ⟨dm ^ 3 / 12, by positivity, ?_⟩
  intro p d hreg hν hmode z g hd
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν
  have hw : p.wOf z ∈ UnforcedLeray.B0412.X p.period p.ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.Cons.C03.Concrete.cw_mem_X z
  have hD : p.wOf z ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.B0412.X_le_D hw
  have h52 : (5 / 2 : ℝ≥0∞) < UnforcedLeray.B0412.q0E := by
    unfold UnforcedLeray.B0412.q0E
    rw [show (5 / 2 : ℝ≥0∞) = ENNReal.ofReal (5 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [UnforcedLeray.B0281.q0_eq])).2
      (by norm_num [UnforcedLeray.B0281.q0_eq])
  obtain ⟨C, -, hS⟩ := UnforcedLeray.Short.PartIIa.graphSupEmbedding
    UnforcedLeray.B0412.q0E h52 UnforcedLeray.B0412.q0E_ne_top
  obtain ⟨W, -, hWae, hWb⟩ := hS p.period hP1 p.ν p.ν_pos ⟨p.wOf z, hD⟩
  refine ⟨|C * p.ν ^ (-(3 / (2 * UnforcedLeray.B0412.q0E.toReal))) *
    UnforcedLeray.B0411.graphNormD (⟨p.wOf z, hD⟩ : UnforcedLeray.B0411.D p.period p.ν
      UnforcedLeray.B0412.q0E)|, abs_nonneg _, ?_⟩
  exact rep_ae_bound (p.wOf z) W _ hWae (fun τ y => (hWb τ y).trans (le_abs_self _))

/-- **`GEGradL2p` from the phase-space inequality** (source 2531, 1515-1531). -/
theorem gradL2p_of_hess (hH : GEHess) (hI : GradL2pIBP) : GEGradL2p := by
  refine geRegime_bind hH geSupBound ?_
  intro p z g hd ⟨h, hh⟩ ⟨M, hM0, hM⟩ j
  exact (hI p.period (p.wOf z) g h M hM0 hM hd.2 hh j).1

end UnforcedLeray.Short.PartIIIb.Concrete
