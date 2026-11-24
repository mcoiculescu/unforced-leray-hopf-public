import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs

/-!
# `PartIII-a:T21/2/7/2/1/2`: regularity of the weak reverse-time adjoint up to the end age

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071: the
reverse-time adjoint `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` is evolved from the terminal age `s` DOWN
to the age `t`, and its weighted energies `E_j` (squared `H^j_{-m}` norms) satisfy
`E_0' + β_min E_1 ≤ C_b E_0`, `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)` in the reverse time; lines
3052-3058: the adjoint localized interaction `K_c^T(φ∇E)` is of order `-1`.

## Truth at the end age, including `t = 0`

In the reverse time `ζ = s - r` the age `t` is the END of the parabolic evolution, the top of every
parabolic cylinder `(r₀ - ρ², r₀] ↦ [t, t + ρ²)`: interior parabolic estimates need a cutoff that
vanishes near the start `r = s` of the reverse evolution only, so they hold up to `r = t`. The
coefficients are needed on `[t, s] × ℝ²` only, and the train is smooth on `[0, ∞) × ℝ²`, one-sided
at the age `0` (`B0140.IsTrain.smooth_v`, `ContDiffOn ℝ ∞ … (Ici 0 ×ˢ univ)`; the datum at age `0`
is the periodized Gaussian, `IsTrain.initial`). So `AdjointEndpointSmooth m` is true also at
`t = 0`; no refutation or weakening at the end age is needed.

## The decomposition

The given version `φ'` is smooth on the open set `(t, s) × ℝ²`; what has to be shown is that it
extends smoothly to `r = t` and that the extension is still a version of `φ` at the age `t`.
* `AdjEndJets m` (the PDE content, SP 3060-3071): every jet `D^n φ'` (in `(r, x)` jointly) is bounded
  on `(t, t + δ) × {‖x‖ ≤ R}`. It is equivalent to `AdjointEndpointSmooth m` given the two calculus
  leaves (a jet of a function smooth on `[t, s) × ℝ²` is continuous up to `t`), so it is a true
  statement.
* `EndExtCont`, `EndExtDeriv` (calculus): bounded jets near `t` give a continuous extension
  `endExt t h` to `[t, s) × ℝ²` (the limit from above at `r = t`; the first jet makes every slice
  `r ↦ h(r, x)` Lipschitz near `t`), and the extension of `h` has derivative within
  `[t, s) × ℝ²` equal to the extension of `fderiv h` (`hasFDerivWithinAt_closure_of_tendsto_fderiv`
  on the convex open set `(t, (t+s)/2) × ℝ²`). `endExt_contDiffOn` (proved here) iterates them:
  `endExt t h` is `C^∞` on `[t, s) × ℝ²`.
* `EndAgeAeCell` (measure theory, `IsAdjointWeak.strongCont` at `t`): the end slice of a continuous
  extension agrees with `φ t` almost everywhere on the cell; `periodicAeOfCell` (proved here) passes
  to the plane for periodic functions (the cell is a fundamental domain,
  `Cyl.isAddFundamentalDomain_cell`).
* `adjointEndpointSmooth_of` (proved here) assembles them; the end slice is periodic because it is
  the limit of the periodic slices (`adjPeriodic_of_ae_eq`).
* `AdjEndJets m` is reduced to the vocabulary of the interior design (`Sub/AdjInterior/Defs.lean`),
  in the same two steps as the interior: `adjEndJets_of` (the identity onto the `BUC` form
  `AdjEndJetsBUC`) and `adjEndJetsBUC_of` (from the train jets `TrainSTJetsOfBUC`, the
  differentiated weak equation `AdjTestedDerivOf`, the weighted bootstrap and the time jets on
  `[t, s)`, `AdjHkStepEnd`, `AdjTimeJetsEnd` — the `[t, s)` forms of `AdjHkStep`, `AdjTimeJetsOf` —
  and the passage from the time jets to classical jets, `EndJetBddOfTimeJets`, from
  `TimeJetPartialBdd` and `JetNormOfPartials` by `endJetBddOfTimeJets_of`), all proved here.
  `adjointInteriorSmoothBUC_of_end` (proved here) derives the interior statement from the same
  `[t, s)` leaves, so one bootstrap serves both.

## The train hypothesis

`AdjEndJets` asks for jets of every order in the age `r`. The age derivatives of the localized
interaction, `∂_r^ℓ K_c^T(φ∇E)`, are `K_c^T` of `φ ∂_r^ℓ∇E + …`, paired against `φ ∈ X_{-m}` only:
they need the weighted decay of the mixed age/space jets of the train (SP 2866-2870, "every fixed
weighted derivative norm"; SP 429-461 at fixed parameters, `sct:heat`). The hypothesis `LadTrainBdd`
records `sup |v|` and `⟨x⟩^{m+2}|∇E|` only. For coefficients that are merely smooth with
`⟨η⟩^{M}|∇E|` bounded the age derivatives of `∇E` need not stay bounded at `t`:
`E = ⟨η⟩^{-M} β(e^{η²}(r - t))`, `β ∈ C_c^∞`, `β = 1` near `0`, is smooth on `ℝ × ℝ²` with
`⟨η⟩^{M-1}|∇E|` bounded, but `sup_x |∂_r∇E(r, x)| → ∞` as `r → t+` (at `e^{η²}(r - t) = u₀` the
factor `e^{η²} = u₀/(r - t)` beats every power of `η`). So `AdjEndJets`, like
`AdjointEndpointSmooth` and the rest of the smoothing chain (`PartIII-a:T21/2/7/2/1/1/1/org`), is
stated for the train of the source, the `BUC` class `PartI.IsBUCTrain` (SP 270-288), with the bounds
`LadTrainBdd`; its weighted space-time jets are `TrainSTJets` (`TrainSTJetsOfBUC`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The extension to the end age -/

/-- The extension of a field `h` on `(t, s) × ℝ²` to the end age `t`: at `r = t` the limit from
above `lim_{r → t+} h(r, x)` (`limUnder`), elsewhere `h` itself. -/
def endExt {F : Type*} [NormedAddCommGroup F] (t : ℝ) (h : ℝ × (ℝ × ℝ) → F)
    (p : ℝ × (ℝ × ℝ)) : F :=
  if p.1 = t then limUnder (𝓝[>] t) (fun r => h (r, p.2)) else h p

/-- All jets of `h` (jointly in `(r, x)`) are bounded near the end age `t`, locally in space: for
every order `n` and radius `R` there are `δ > 0` and `C` with `‖D^n h(r, x)‖ ≤ C` for
`t < r < t + δ`, `‖x‖ ≤ R`. -/
def EndJetBdd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (t : ℝ)
    (h : ℝ × (ℝ × ℝ) → F) : Prop :=
  ∀ n : ℕ, ∀ R : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ r ∈ Ioo t (t + δ), ∀ x : ℝ × ℝ, ‖x‖ ≤ R →
    ‖iteratedFDeriv ℝ n h (r, x)‖ ≤ C

/-- **Continuity of the extension** (calculus): a field `C^∞` on `(t, s) × ℝ²` with bounded jets
near `t` (complete target) extends continuously to `[t, s) × ℝ²`. (With `n = 1`, `‖fderiv h‖ ≤ C`
on the convex open set `(t, t + δ') × ball 0 R`, so `h` is `C`-Lipschitz there; the slices
`r ↦ h(r, x)` are Cauchy as `r → t+`, the limit `endExt t h (t, x)` exists, and
`‖endExt t h (r, x) - endExt t h (t, x₀)‖ ≤ C(r - t) + C‖x - x₀‖`.) -/
def EndExtCont : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (t s : ℝ), t < s →
    ∀ h : ℝ × (ℝ × ℝ) → F, ContDiffOn ℝ ∞ h (Ioo t s ×ˢ univ) → EndJetBdd t h →
      ContinuousOn (endExt t h) (Ico t s ×ˢ univ)

/-- **The derivative of the extension** (calculus): if `h` is differentiable on `(t, s) × ℝ²` and
both `h` and `fderiv h` extend continuously to `[t, s) × ℝ²`, then the extension of `h` has, within
`[t, s) × ℝ²`, the derivative given by the extension of `fderiv h`. (Away from `r = t` the
extension is `h` near the point; at `(t, x)` apply `hasFDerivWithinAt_closure_of_tendsto_fderiv` on
the convex open set `(t, (t+s)/2) × ℝ²`, whose closure agrees with `[t, s) × ℝ²` near `(t, x)`.) -/
def EndExtDeriv : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (t s : ℝ), t < s →
    ∀ h : ℝ × (ℝ × ℝ) → F, DifferentiableOn ℝ h (Ioo t s ×ˢ univ) →
      ContinuousOn (endExt t h) (Ico t s ×ˢ univ) →
      ContinuousOn (endExt t (fderiv ℝ h)) (Ico t s ×ˢ univ) →
      ∀ p ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)),
        HasFDerivWithinAt (endExt t h) (endExt t (fderiv ℝ h) p) (Ico t s ×ˢ univ) p

/-- **The extension is smooth up to the end age**, order by order: from `EndExtCont` and
`EndExtDeriv`, by induction on the order with the target space generalized (the derivative of the
extension is the extension of the derivative, whose jets are those of `h` shifted by one,
`norm_iteratedFDeriv_fderiv`). -/
theorem endExt_contDiffOn (h2 : EndExtCont) (h3 : EndExtDeriv) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (t s : ℝ), t < s →
      ∀ h : ℝ × (ℝ × ℝ) → F, ContDiffOn ℝ ∞ h (Ioo t s ×ˢ univ) → EndJetBdd t h →
        ContDiffOn ℝ n (endExt t h) (Ico t s ×ˢ univ) := by
  induction n with
  | zero =>
    intro F _ _ _ t s hts h hh hb
    exact contDiffOn_zero.mpr (h2 F t s hts h hh hb)
  | succ n ih =>
    intro F _ _ _ t s hts h hh hb
    have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
    have hS : UniqueDiffOn ℝ (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) :=
      (uniqueDiffOn_Ico t s).prod uniqueDiffOn_univ
    have hh' : ContDiffOn ℝ ∞ (fderiv ℝ h) (Ioo t s ×ˢ univ) :=
      hh.fderiv_of_isOpen hU (by simp)
    have hb' : EndJetBdd t (fderiv ℝ h) := by
      intro k R
      obtain ⟨δ, hδ, C, hC⟩ := hb (k + 1) R
      exact ⟨δ, hδ, C, fun r hr x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hC r hr x hx⟩
    have hd := h3 F t s hts h (hh.differentiableOn (by simp)) (h2 F t s hts h hh hb)
      (h2 _ t s hts (fderiv ℝ h) hh' hb')
    have heq : ∀ p ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)),
        fderivWithin ℝ (endExt t h) (Ico t s ×ˢ univ) p = endExt t (fderiv ℝ h) p :=
      fun p hp => (hd p hp).fderivWithin (hS p hp)
    have key := contDiffOn_succ_of_fderivWithin (n := ((n : ℕ) : ℕ∞ω))
      (fun p hp => (hd p hp).differentiableWithinAt) (fun hω => absurd hω (by simp))
      ((ih _ t s hts (fderiv ℝ h) hh' hb').congr heq)
    exact_mod_cast key

/-- A slice of a function continuous on `[t, s) × ℝ²` is continuous. -/
theorem endSlice_continuous {g : ℝ × (ℝ × ℝ) → ℂ} {t s : ℝ}
    (hg : ContinuousOn g (Ico t s ×ˢ univ)) {r : ℝ} (hr : r ∈ Ico t s) :
    Continuous fun x : ℝ × ℝ => g (r, x) :=
  hg.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hr, mem_univ x⟩

/-- The end slice of a function continuous on `[t, s) × ℝ²` is the limit from above of the
slices. -/
theorem endSlice_tendsto {g : ℝ × (ℝ × ℝ) → ℂ} {t s : ℝ} (hts : t < s)
    (hg : ContinuousOn g (Ico t s ×ˢ univ)) (x : ℝ × ℝ) :
    Tendsto (fun r => g (r, x)) (𝓝[>] t) (𝓝 (g (t, x))) := by
  have hc : ContinuousWithinAt g (Ico t s ×ˢ univ) (t, x) :=
    hg (t, x) ⟨⟨le_rfl, hts⟩, mem_univ x⟩
  have hmap : Tendsto (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) (𝓝[>] t)
      (𝓝[Ico t s ×ˢ univ] (t, x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
        ((r, x) : ℝ × (ℝ × ℝ))) t)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hts] with r hr
      exact ⟨Ioo_subset_Ico_self hr, mem_univ x⟩
  exact hc.tendsto.comp hmap

/-- The end slice of a function continuous on `[t, s) × ℝ²` whose slices before `s` are periodic
is periodic (limit of the periodic slices). -/
theorem endSlice_periodic {g : ℝ × (ℝ × ℝ) → ℂ} {t s c : ℝ} (hts : t < s)
    (hg : ContinuousOn g (Ico t s ×ˢ univ))
    (hper : ∀ r ∈ Ioo t s, ∀ x : ℝ × ℝ, g (r, (x.1 + c, x.2)) = g (r, x)) (x : ℝ × ℝ) :
    g (t, (x.1 + c, x.2)) = g (t, x) := by
  have h1 := endSlice_tendsto hts hg (x.1 + c, x.2)
  have h2 := endSlice_tendsto hts hg x
  have heq : (fun r => g (r, (x.1 + c, x.2))) =ᶠ[𝓝[>] t] fun r => g (r, x) := by
    filter_upwards [Ioo_mem_nhdsGT hts] with r hr using hper r hr x
  exact tendsto_nhds_unique (h1.congr' heq) h2

/-! ## The end slice is a version of `φ t` -/

/-- **The end slice agrees with the weak solution on the cell** (measure theory; the strong
continuity `IsAdjointWeak.strongCont` at the end age, SP 3060): if `g` is continuous on
`[t, s) × ℝ²`, its slices before `s` are versions of `φ r`, and `φ r → φ t` in `X_{-m,c}` as
`r → t+`, then `g(t, ·) = φ t` almost everywhere on the cell. (Choose `r_n ↓ t`; `L²` convergence in
`cellMeasure c (-m)` gives an a.e. convergent subsequence, `tendstoInMeasure_of_tendsto_eLpNorm`,
`TendstoInMeasure.exists_seq_tendsto_ae`; `g(r_n, x) → g(t, x)` for every `x`
(`endSlice_tendsto`); the countably many versions agree a.e. (`ae_all_iff`); the cell measure and
Lebesgue measure on the cell are equivalent, `B0579.ac_cellMeasure`.) -/
def EndAgeAeCell : Prop :=
  ∀ (c m t s : ℝ), t < s → ∀ (φ : ℝ → ℝ × ℝ → ℂ) (g : ℝ × (ℝ × ℝ) → ℂ),
    ContinuousOn g (Ico t s ×ˢ univ) →
    (∀ r ∈ Ioo t s, (fun x => g (r, x)) =ᵐ[volume] φ r) →
    MemLp (φ t) 2 (B0579.cellMeasure c (-m)) →
    Tendsto (fun r => xNorm c (-m) (φ r - φ t)) (𝓝[Ioo t s] t) (𝓝 0) →
    (fun x => g (t, x)) =ᵐ[volume.restrict (B0579.cell c)] φ t

/-- **Periodic functions equal on the cell are equal on the plane** (the cell `[-c/2, c/2) × ℝ` is a
fundamental domain of `q ↦ q + cℤ`). -/
def PeriodicAeOfCell : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f g : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) →
    f =ᵐ[volume.restrict (B0579.cell c)] g → f =ᵐ[volume] g

theorem periodicAeOfCell : PeriodicAeOfCell := by
  intro c hc f g hf hg hfg
  have hf' : UnforcedLeray.Cyl.IsPeriodic c f := hf
  have hg' : UnforcedLeray.Cyl.IsPeriodic c g := hg
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    simp only [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  let S : Set (ℝ × ℝ) := {z | f z ≠ g z}
  have hcenter : volume (S ∩ UnforcedLeray.Cyl.cell c) = 0 := by
    rw [hcell] at hfg
    have hzero : volume.restrict (UnforcedLeray.Cyl.cell c) S = 0 := by
      simpa [S] using ae_iff.mp hfg
    rw [Measure.restrict_apply' (UnforcedLeray.Cyl.measurableSet_cell c)] at hzero
    exact hzero
  have hnull := (UnforcedLeray.Cyl.isAddFundamentalDomain_cell hc).measure_zero_of_invariant
    S ?_ hcenter
  · exact ae_iff.mpr (by simpa [S] using hnull)
  · intro v
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [S, Set.mem_ofPred_eq]
    rw [hf'.vadd_zmultiples, hg'.vadd_zmultiples]

/-! ## The parabolic content -/

/-- **Bounded jets up to the end age** (SP 3060-3071; the reverse evolution runs from `s` down to
`t`, so `t` is the top of the parabolic cylinders and the local estimates hold up to it; the
coefficients are smooth on `[0, ∞) × ℝ²`, one-sided at `0`, `B0140.IsTrain.smooth_v`). For `ν ≤ 1`,
a BUC train (`PartI.IsBUCTrain`, SP 270-288) with the bounds `LadTrainBdd`, a weak adjoint `φ` with
terminal datum `physAdj a_s G` and a version `φ'` of it which is jointly `C^∞` on `(t, s) × ℝ²`:
every jet `D^n φ'` (in `(r, x)`) is bounded on `(t, t + δ) × {‖x‖ ≤ R}` for some `δ > 0`. The age
jets need the weighted space-time jets of the train of every order (SP 2866-2870), which
`LadTrainBdd` does not record and the BUC train has (`TrainSTJetsOfBUC`; see the module
docstring). -/
def AdjEndJets (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∀ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] φ r) →
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
          EndJetBdd t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2)

/-! ## The assembly -/

/-- **Regularity up to the end age** from the bounded jets (`AdjEndJets`), the calculus of the
extension (`EndExtCont`, `EndExtDeriv`) and the identification of the end slice (`EndAgeAeCell`):
`φ''(r) = endExt t φ'(r, ·)` is `C^∞` on `[t, s) × ℝ²`, equals `φ' r` for `r ∈ (t, s)`, and its end
slice is periodic and agrees with `φ t` on the cell, hence on the plane. -/
theorem adjointEndpointSmooth_of (m : ℝ) (h1 : AdjEndJets m) (h2 : EndExtCont)
    (h3 : EndExtDeriv) (h4 : EndAgeAeCell) : AdjointEndpointSmooth m := by
  intro ν hν hν1 tr htr hb t s ht hts G hG φ hφ φ' hae hsm
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hJ := h1 ν hν hν1 tr htr hb t s ht hts G hG φ hφ φ' hae hsm
  have hg : ContDiffOn ℝ ∞ (endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2)) (Ico t s ×ˢ univ) :=
    contDiffOn_infty.2 fun n => endExt_contDiffOn h2 h3 n ℂ t s hts _ hsm hJ
  have hgc := hg.continuousOn
  have hEq : ∀ r ∈ Ioo t s,
      (fun x => endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (r, x)) = φ' r := by
    intro r hr
    funext x
    simp [endExt, hr.1.ne']
  have hae' : ∀ r ∈ Ioo t s,
      (fun x => endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (r, x)) =ᵐ[volume] φ r := by
    intro r hr
    rw [hEq r hr]
    exact hae r hr
  refine ⟨fun r x => endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (r, x), fun r hr => ?_, hg⟩
  show (fun x => endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (r, x)) =ᵐ[volume] φ r
  by_cases hrt : r = t
  · rw [hrt]
    have hper : ∀ x : ℝ × ℝ,
        endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (t, (x.1 + ν ^ (-2 : ℝ), x.2)) =
          endExt t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (t, x) := by
      refine endSlice_periodic hts hgc (fun r' hr' x => ?_)
      exact adjPeriodic_of_ae_eq (endSlice_continuous hgc (Ioo_subset_Ico_self hr'))
        (hae' r' hr') (hφ.periodic r' (Ioo_subset_Ico_self hr')) x
    have hcell := h4 (ν ^ (-2 : ℝ)) m t s hts φ _ hgc hae' (hφ.memX t ⟨le_rfl, hts.le⟩)
      (tendsto_nhdsWithin_mono_left Ioo_subset_Icc_self (hφ.strongCont t ⟨le_rfl, hts.le⟩))
    exact periodicAeOfCell (ν ^ (-2 : ℝ)) hc _ _ hper (hφ.periodic t ⟨le_rfl, hts⟩) hcell
  · exact hae' r ⟨lt_of_le_of_ne hr.1 (Ne.symm hrt), hr.2⟩

/-! ## The bounded jets in the weighted scale

The vocabulary is that of the interior design (`Sub/AdjInterior/Defs.lean`,
`PartIII-a:T21/2/7/2/1/1/org`): the weighted jets `TrainSTJets` of the train (from `TrainBUCOfBdd`
and `TrainSTJetsOfBUC`), the differentiated weak equation `AdjTestedDeriv` (`AdjTestedDerivOf`), the
weighted classes `AdjHkOn` (`C(I; H^k_{-m,c})`) and the time jets `IsAdjTimeJets`. The end age only
changes the interval: `[t, s)` in place of `(t, s)`. -/

/-- The base `k = 0` on `[t, s)`: a weak adjoint lies in `C([t, s); X_{-m,c})` (the fields `memX`,
`periodic`, `strongCont` of `IsAdjointWeak`). -/
theorem adjHkOn_zero_Ico_of_weak {ν c m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {t s : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ} (hφ : IsAdjointWeak ν c m tr t s g φ) :
    AdjHkOn c m 0 (Ico t s) φ := by
  refine ⟨fun r _ => φ r, fun r hr => ⟨rfl, fun _ _ x => hφ.periodic r hr x,
    fun _ _ => hφ.memX r ⟨hr.1, hr.2.le⟩, fun _ _ hw => absurd hw (Nat.not_lt_zero _)⟩,
    fun _ _ r hr => ?_⟩
  exact (hφ.strongCont r ⟨hr.1, hr.2.le⟩).mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)

/-- `C(I; H^k_{-m,c})` restricts to subsets. -/
theorem AdjHkOn.mono {c m : ℝ} {k : ℕ} {I J : Set ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (h : AdjHkOn c m k I φ) (hJI : J ⊆ I) : AdjHkOn c m k J φ := by
  obtain ⟨D, hD, hc⟩ := h
  exact ⟨D, fun r hr => hD r (hJI hr),
    fun w hw r hr => (hc w hw r (hJI hr)).mono_left (nhdsWithin_mono _ hJI)⟩

/-- Time jets restrict to subsets. -/
theorem IsAdjTimeJets.mono {c m : ℝ} {I J : Set ℝ} {Φ : ℕ → ℝ → ℝ × ℝ → ℂ}
    (h : IsAdjTimeJets c m I Φ) (hJI : J ⊆ I) : IsAdjTimeJets c m J Φ :=
  ⟨fun j k => (h.1 j k).mono hJI, fun j r hr =>
    (h.2 j r (hJI hr)).mono_left (nhdsWithin_mono _ (Set.sdiff_subset_sdiff_left hJI))⟩

/-- **The bootstrap step up to the end age** (SP 3060-3071 with SP 3052-3058; `AdjHkStep` of
`Sub/AdjInterior/Defs.lean` on `[t, s)` in place of `(t, s)`): a weak adjoint in
`C([t, s); H^k_{-m,c})` lies in `C([t, s); H^{k+1}_{-m,c})`. The weighted energies satisfy
`E_j' + βE_{j+1} ≤ C(E_j + ⋯ + E_0)` in the reverse time `ζ = s - r`; the time cutoff is needed near
the START `r = s` of the reverse evolution only, so the estimate on `[t, b]`, `b < s`, uses the
weak identity up to the end age `r = t` (`IsAdjointWeak.weak` and `AdjTestedDeriv` hold on
`[t, s]`). -/
def AdjHkStepEnd (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ico t s) φ →
        AdjHkOn (ν ^ (-2 : ℝ)) m (k + 1) (Ico t s) φ

/-- **The time jets up to the end age** (SP 3060; `AdjTimeJetsOf` of `Sub/AdjInterior/Defs.lean`
on `[t, s)`): a weak adjoint in `C([t, s); H^k_{-m,c})` for every `k` has time jets on `[t, s)`
(one-sided at `t`), `Φ 0 = φ`, `Φ (j + 1) = ∂_r Φ j` within `[t, s)` from the equation
`-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)` and the space-time jets of the train. -/
def AdjTimeJetsEnd (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      (∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ico t s) φ) →
      ∃ Φ : ℕ → ℝ → ℝ × ℝ → ℂ, Φ 0 = φ ∧ IsAdjTimeJets (ν ^ (-2 : ℝ)) m (Ico t s) Φ

/-- The classical mixed partial `∂^w ∂_r^j φ'(r, x)` of a field on space-time: `j` derivatives in
the age (`iteratedDeriv` of the slice `r ↦ φ'(r, y)`), then the spatial word `w` (`adjSpatial`). -/
def stPartial (φ' : ℝ → ℝ × ℝ → ℂ) (j : ℕ) (w : List (Fin 2)) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  adjSpatial w (fun y => iteratedDeriv j (fun r' => φ' r' y) r) x

/-- **Classical partials from the time jets, uniformly up to the end age** (analysis): if `Φ` are
time jets on `[t, s)` and `φ'` is a version of `Φ 0` jointly `C^∞` on `(t, s) × ℝ²`, then for every
order `n` and radius `R` the partials `∂^w ∂_r^j φ'`, `j ≤ n`, `|w| ≤ n`, are bounded on
`(t, t + δ) × {‖x‖ ≤ R}`. (i) For `r ∈ (t, s)`: `∂_r^j φ'(r) = Φ j r` almost everywhere (induction on
`j`: the classical difference quotients converge pointwise, those of `Φ j` in `X_{-m,c}`, so along a
subsequence almost everywhere; both sides are `c`-periodic), and `∂^w` of it is the weak derivative
field `D r w` of `IsCellJet` (classical derivatives are weak derivatives on the cylinder; weak
derivatives are unique almost everywhere). (ii) For a smooth `c`-periodic `g`,
`sup_{‖x‖ ≤ R} |g| ≤ C_R Σ_{|w| ≤ 2} ‖∂^w g‖_{X_{-m,c}}` (cutoff, `g = ∫∫ ∂₁∂₂(ζg)`, Cauchy-Schwarz,
finitely many periods, the weight bounded below on compacts). (iii) `r ↦ ‖D r w‖_{X_{-m,c}}` is
continuous on `[t, s)` (`AdjHkOn`), hence bounded on `[t, t + δ]` for `δ < s - t`. -/
def TimeJetPartialBdd : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) (φ' : ℝ → ℝ × ℝ → ℂ), 0 < c → t < s →
    IsAdjTimeJets c m (Ico t s) Φ → (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] Φ 0 r) →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
    ∀ n : ℕ, ∀ R : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ j ≤ n, ∀ w : List (Fin 2), w.length ≤ n →
      ∀ r ∈ Ioo t (t + δ), ∀ x : ℝ × ℝ, ‖x‖ ≤ R → ‖stPartial φ' j w r x‖ ≤ C

/-- **The jet norm by the mixed partials** (calculus): for a field jointly `C^∞` on an open set of
space-time, `‖D^n φ'(p)‖ ≤ C_n Σ_{j ≤ n} Σ_{|w| = n - j} |∂^w ∂_r^j φ'(p)|`. (Expand each argument
in the basis `stDir` (sup norm, coordinates bounded by the norm) by multilinearity; the values on
basis vectors are mixed partials, in any order by symmetry, `ContDiffAt.iteratedFDeriv_comp_perm`;
the age partial of the slice is the `stDir 0` directional derivative. `C_n = 2^n` works.) -/
def JetNormOfPartials : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ (φ' : ℝ → ℝ × ℝ → ℂ) (U : Set (ℝ × (ℝ × ℝ))), IsOpen U →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) U → ∀ p ∈ U,
      ‖iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) p‖ ≤
        C * ∑ j ∈ Finset.range (n + 1), ∑ i : Fin (n - j) → Fin 2,
          ‖stPartial φ' j (List.ofFn i) p.1 p.2‖

/-- **Bounded jets from the time jets**: time jets on `[t, s)` and a smooth version on `(t, s) × ℝ²`
give bounded jets near the end age. -/
def EndJetBddOfTimeJets : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) (φ' : ℝ → ℝ × ℝ → ℂ), 0 < c → t < s →
    IsAdjTimeJets c m (Ico t s) Φ → (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] Φ 0 r) →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
    EndJetBdd t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2)

theorem endJetBddOfTimeJets_of (h1 : TimeJetPartialBdd) (h2 : JetNormOfPartials) :
    EndJetBddOfTimeJets := by
  intro c m t s Φ φ' hc hts hΦ hae hsm n R
  obtain ⟨C₀, hC₀⟩ := h2 n
  obtain ⟨δ, hδ, C, hC⟩ := h1 c m t s Φ φ' hc hts hΦ hae hsm n R
  refine ⟨min δ (s - t), lt_min hδ (sub_pos.2 hts),
    max C₀ 0 * ∑ j ∈ Finset.range (n + 1), ∑ _i : Fin (n - j) → Fin 2, C, fun r hr x hx => ?_⟩
  have hrU : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨⟨hr.1, by linarith [hr.2, min_le_right δ (s - t)]⟩, mem_univ x⟩
  have hr' : r ∈ Ioo t (t + δ) := ⟨hr.1, by linarith [hr.2, min_le_left δ (s - t)]⟩
  have key := hC₀ φ' _ (isOpen_Ioo.prod isOpen_univ) hsm (r, x) hrU
  have hS : ∑ j ∈ Finset.range (n + 1), ∑ i : Fin (n - j) → Fin 2,
        ‖stPartial φ' j (List.ofFn i) r x‖ ≤
      ∑ j ∈ Finset.range (n + 1), ∑ _i : Fin (n - j) → Fin 2, C := by
    refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i _ => ?_
    exact hC j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (List.ofFn i)
      (by rw [List.length_ofFn]; exact Nat.sub_le n j) r hr' x hx
  have hS0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∑ i : Fin (n - j) → Fin 2,
      ‖stPartial φ' j (List.ofFn i) r x‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖iteratedFDeriv ℝ n (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (r, x)‖
      ≤ C₀ * ∑ j ∈ Finset.range (n + 1), ∑ i : Fin (n - j) → Fin 2,
          ‖stPartial φ' j (List.ofFn i) r x‖ := key
    _ ≤ max C₀ 0 * ∑ j ∈ Finset.range (n + 1), ∑ i : Fin (n - j) → Fin 2,
          ‖stPartial φ' j (List.ofFn i) r x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    _ ≤ max C₀ 0 * ∑ j ∈ Finset.range (n + 1), ∑ _i : Fin (n - j) → Fin 2, C :=
          mul_le_mul_of_nonneg_left hS (le_max_right _ _)

/-- The `BUC` form of the bounded end jets (the form of `AdjointInteriorSmoothBUC`,
`Sub/AdjInterior/Defs.lean`), the conclusion of `adjEndJetsBUC_of`; `adjEndJets_of` identifies it
with `AdjEndJets m`. -/
def AdjEndJetsBUC (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∀ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] φ r) →
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
          EndJetBdd t (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2)

/-- `AdjEndJets m` is the `BUC` form `AdjEndJetsBUC m` (both are for the trains of
`PartI.IsBUCTrain` with the bounds `LadTrainBdd`; as `adjointInteriorSmooth_of`,
`Sub/AdjInterior/Assembly.lean`). -/
theorem adjEndJets_of (m : ℝ) (h1 : AdjEndJetsBUC m) : AdjEndJets m := by
  intro ν hν hν1 tr htr hB
  exact h1 ν hν hν1 tr htr hB

/-- **Bounded jets up to the end age from the weighted scale** (`BUC` trains): the train jets
(`TrainSTJetsOfBUC`), the differentiated weak equation (`AdjTestedDerivOf`), the bootstrap on
`[t, s)` (`AdjHkStepEnd`, by induction from `adjHkOn_zero_Ico_of_weak`), the time jets on `[t, s)`
(`AdjTimeJetsEnd`) and the passage to classical jets (`EndJetBddOfTimeJets`). -/
theorem adjEndJetsBUC_of (m : ℝ) (h1 : TrainSTJetsOfBUC m)
    (h2 : AdjTestedDerivOf m) (h3 : AdjHkStepEnd m) (h4 : AdjTimeJetsEnd m)
    (h5 : EndJetBddOfTimeJets) : AdjEndJetsBUC m := by
  intro ν hν hν1 tr hbuc hB t s ht hts G _ φ hφ φ' hae hsm
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hJ : ∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S := h1 ν hν hν1 tr hbuc hB
  have hD : AdjTestedDeriv tr t s φ := h2 ν hν hν1 tr hB t s ht hts _ φ hφ
  have hk : ∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ico t s) φ := by
    intro k
    induction k with
    | zero => exact adjHkOn_zero_Ico_of_weak hφ
    | succ k ih => exact h3 ν hν hν1 tr hB hJ t s ht hts _ φ hφ hD k ih
  obtain ⟨Φ, hΦ0, hΦ⟩ := h4 ν hν hν1 tr hB hJ t s ht hts _ φ hφ hD hk
  exact h5 _ m t s Φ φ' hc hts hΦ (fun r hr => by rw [hΦ0]; exact hae r hr) hsm

/-- **The interior statement from the same leaves**: `AdjointInteriorSmoothBUC m` (of
`Sub/AdjInterior/Defs.lean`) follows from the `[t, s)` leaves `AdjHkStepEnd`, `AdjTimeJetsEnd`
restricted to `(t, s)` (`AdjHkOn.mono`, `IsAdjTimeJets.mono`) and the interior Sobolev leaves, so the
`(t, s)` leaves `AdjHkStep`, `AdjTimeJetsOf` need not be proved separately. -/
theorem adjointInteriorSmoothBUC_of_end (m : ℝ) (h0 : TrainSTJetsOfBUC m)
    (h1 : AdjTestedDerivOf m) (h2 : AdjHkStepEnd m) (h3 : AdjTimeJetsEnd m)
    (h4 : TimeJetsSTSobolev) (h5 : STSobolevSmoothRep) (h6 : STRepSliceAe) :
    AdjointInteriorSmoothBUC m := by
  intro ν hν hν1 tr hbuc hB t s ht hts G _ φ hφ
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hJ : ∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S := h0 ν hν hν1 tr hbuc hB
  have hD : AdjTestedDeriv tr t s φ := h1 ν hν hν1 tr hB t s ht hts _ φ hφ
  have hk : ∀ k : ℕ, AdjHkOn (ν ^ (-2 : ℝ)) m k (Ico t s) φ := by
    intro k
    induction k with
    | zero => exact adjHkOn_zero_Ico_of_weak hφ
    | succ k ih => exact h2 ν hν hν1 tr hB hJ t s ht hts _ φ hφ hD k ih
  obtain ⟨Φ, hΦ0, hΦ⟩ := h3 ν hν hν1 tr hB hJ t s ht hts _ φ hφ hD hk
  have hΦ' := hΦ.mono Ioo_subset_Ico_self
  obtain ⟨F, hFsl, hFS⟩ := h4 _ m t s Φ hc hts hΦ'
  obtain ⟨F', hF', hF'ae⟩ := h5 _ _ F hFS
  have hsl := h6 _ m t s (Φ 0) F F' hc hts (hΦ'.1 0 0) hFsl hF'.continuousOn hF'ae
  refine ⟨fun r x => F' (r, x), fun r hr => ?_, hF'⟩
  have h := hsl r hr
  rwa [hΦ0] at h

end UnforcedLeray.Short.IIIa
