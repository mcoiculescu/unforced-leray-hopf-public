import UnforcedLeray.Lib.ComplexODE
import UnforcedLeray.Lib.ComplexODEB.Bifurcation
import UnforcedLeray.Lib.ComplexODEB.RealLimit
import UnforcedLeray.Lib.ComplexODEB.AnnulusToPlane
import UnforcedLeray.Analysis.Rayleigh.Normalization

/-!
# Linear ODE with complex parameters, part 2: Lin's continuation and the whole-line mode
(Wave 2 block 2H PLAN1b: INF18 O4–O8)

Main file of the second INF18 layer of the Lean build plan

O4–O8 in `scoping/INF10-INF12-INF18-Planar.md` §5 Level O, bypass B8 route A). It builds on
`Lib/ComplexODE` (O1–O3) and on the compiled Evans framework
(`lean/UnforcedLeray/Analysis/Rayleigh/Evans/*`, `WholeLineLimit`, `ClassicalMode`,
`RealSpeed/*`). Blueprint units B0034 (`paper/main.tex` lines 1012--1021, eq. `st18-t00033`),
B0035--B0041 (lines 1022--1086) and B0042--B0045 (lines 1088--1121, eqs.
`st18-t00040`--`st18-t00042`).

Setting. `evansFunction β a b c = F(b)` where `F'' = (β² + A/(Ω - c)) F`, `F(a) = 0`,
`F'(a) = 1` (logarithmic radius, compiled `Evans.Solution`); for `Im c > 0` its zeros are the
Dirichlet modes on `[a, b]`. `neutralEvansFunction α a b` is the same at `c = a_*`, where
`A/(Ω - a_*) = -W` (`Lib/ComplexODE/NeutralSolution`).

| Target | Module | Main declarations |
|---|---|---|
| O4 annular bifurcation (Lin 2003, Thm 5.9) | `ComplexODEB/{Dependence,Cauchy,BifurcationError,Bifurcation}` | `ComplexODEB.bifurcatesBelow_of_neutral`, **`exists_unstable_below_neutral`**, `eventually_exists_unstable_below_neutral` |
| O5 openness (Hurwitz by minimum modulus) | `ComplexODEB/{MinModulus,Coercive,Openness}` | `ComplexODEB.isOpen_unstableWavenumbers`, **`isOpen_annularUnstable`** |
| O6 closedness in `(1, α)` (Lin 2003, Lemma 5.8) | `ComplexODEB/{GroundState,Neutral,Energy,Normalized,RealExclusion,RealLimit,Continuation}` | `ComplexODEB.noRealLimitSpeed_of_neutral`, `closure_annularUnstable_inter_Ioo_subset`, **`annularUnstable_relClosed`** |
| O7 mode at `β = 2` on every large annulus | `ComplexODEB/{NeutralExistence,Continuation}`, this file | `Ioo_subset_annularUnstable`, **`exists_annular_mode_two`** |
| O8 whole-line mode | `ComplexODEB/{WeakRealSpeed,WholeLineMode,AnnulusToPlane}`, this file | `ComplexODEB.wholeLineLimit_speed_im_pos`, `ComplexODEB.exists_normalized_wholeLineMode_of_annular_sequence`, **`exists_wholeLine_growing_mode`** |

Provenance. The O4–O7 helpers are copies of the compiled drafts

copies there replace the drafts `Analysis/Rayleigh/Evans/{NeutralSolution,
L1ContinuousGronwall}`), in namespace `UnforcedLeray.ComplexODEB`. The O8 helpers are


WholeLineNormalization}.lean`. None of the drafts is edited.

Endpoint critical layer (scoping README §6 Q15). The exclusion of real limiting speeds on
the annulus (`ComplexODEB.RealLimitMode.false`, used by `noRealLimitSpeed_of_neutral`)
treats a critical point anywhere in the closed interval `[a, b]`, endpoints included: the
limit vanishes at the critical point (at an endpoint by the Dirichlet condition, inside by
`value_zero_at_critical`), and the ground state `h_c = e^t (Ω - c)` factorizes on each side.
No hypothesis excludes `c_∞ = Ω(±N)`.

Deviations from the scoping signatures (§5 of the scoping note):
* O4 is stated for every neutral wavenumber `α > 1` of `[-N, N]` with `t_* < N`, not only
  for the `α_N` of O1; `eventually_exists_unstable_below_neutral` adds O1's `α_N > 2` and its
  uniqueness.
* O5 assumes `0 < N` (a nondegenerate annulus); O6 names the neutral wavenumber `α` and the
  hypothesis `t_* < N` explicitly.
* O8 gives a classical mode (`Rayleigh.GaussianWholeLineMode`: `C²`, `F, F', F'' ∈ L²`, the
  equation at every `t`) of unit mass, smooth and decaying with `F'`, in place of the weak
  `H²` form of the scoping signature; it implies that form.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff Set.Notation
namespace UnforcedLeray.Rayleigh.Evans
open UnforcedLeray.Sturm

/-- The critical log-radius `t_* = log √8` (tex lines 990--992) lies in `(-N, N)` once
`t_* < N`. -/
theorem neutralCriticalTime_mem_Ioo_neg {N : ℝ} (hN : neutralCriticalTime < N) :
    neutralCriticalTime ∈ Ioo (-N) N :=
  ⟨by linarith [neutralCriticalTime_pos], hN⟩

/-! ### O4: annular bifurcation below a neutral wavenumber -/

/-- O4 on a general log-annulus `[a, b]` containing `t_*` (Lin 2003, Theorem 5.9, as used
at tex lines 1012--1014): below every neutral wavenumber `α > 1` there is an interval of
unstable wavenumbers. -/
theorem exists_unstable_below_neutral_of_mem {a b α : ℝ} (hα : 1 < α)
    (hcrit : neutralCriticalTime ∈ Ioo a b) (hneut : neutralEvansFunction α a b = 0) :
    ∃ δ > 0, ∀ β ∈ Ioo (α - δ) α, ∃ c : ℂ, 0 < c.im ∧ evansFunction β a b c = 0 :=
  ComplexODEB.bifurcatesBelow_of_neutral hα hcrit
    ((ComplexODEB.neutralEvansFunction_eq_zero_iff α a b).mp hneut)

/-- O4 (blueprint B0034, tex lines 1012--1014; scoping `exists_unstable_below_neutral`):
on `[-N, N]` with `t_* < N`, every neutral wavenumber `α > 1` has unstable wavenumbers
`β ∈ (α - δ, α)` just below it. -/
theorem exists_unstable_below_neutral {N α : ℝ} (hN : neutralCriticalTime < N) (hα : 1 < α)
    (hneut : neutralEvansFunction α (-N) N = 0) :
    ∃ δ > 0, ∀ β ∈ Ioo (α - δ) α, ∃ c : ℂ, 0 < c.im ∧ evansFunction β (-N) N c = 0 :=
  exists_unstable_below_neutral_of_mem hα (neutralCriticalTime_mem_Ioo_neg hN) hneut

/-- O4 combined with O1 (`exists_dirichlet_neutral`, tex lines 1001--1014): on every large
log-annulus the neutral wavenumber `α_N > 2` is unique above one and bifurcates. -/
theorem eventually_exists_unstable_below_neutral : ∀ᶠ N : ℝ in atTop, ∃ αN : ℝ, 2 < αN ∧
    neutralEvansFunction αN (-N) N = 0 ∧
    (∀ β : ℝ, 1 < β → neutralEvansFunction β (-N) N = 0 → β = αN) ∧
    ∃ δ > 0, ∀ β ∈ Ioo (αN - δ) αN, ∃ c : ℂ, 0 < c.im ∧ evansFunction β (-N) N c = 0 := by
  filter_upwards [exists_dirichlet_neutral, eventually_gt_atTop neutralCriticalTime]
    with N hN hNt
  obtain ⟨αN, hα2, hneut, huniq, -, -⟩ := hN
  exact ⟨αN, hα2, hneut, huniq, exists_unstable_below_neutral hNt (by linarith) hneut⟩

/-! ### O5: openness -/

/-- The unstable wavenumbers above one of the log-annulus `[-N, N]`: real `β > 1` for which
the Rayleigh–Dirichlet problem has an eigenvalue `c` with `Im c > 0`. -/
def annularUnstable (N : ℝ) : Set ℝ :=
  {β : ℝ | 1 < β ∧ ∃ c : ℂ, 0 < c.im ∧ evansFunction β (-N) N c = 0}

theorem annularUnstable_eq (N : ℝ) :
    annularUnstable N = Ioi 1 ∩ ComplexODEB.unstableWavenumbers (-N) N := by
  ext β
  simp only [annularUnstable, ComplexODEB.unstableWavenumbers, mem_ofPred_eq, mem_inter_iff,
    mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (lt_trans one_pos h1).ne', h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

/-- O5 (scoping `isOpen_annularUnstable`; Hurwitz openness in Lin's continuation, tex lines
1012--1014): the unstable wavenumbers above one form an open set. -/
theorem isOpen_annularUnstable {N : ℝ} (hN : 0 < N) : IsOpen (annularUnstable N) := by
  rw [annularUnstable_eq]
  exact isOpen_Ioi.inter (ComplexODEB.isOpen_unstableWavenumbers (by linarith))

/-! ### O6: closedness in `(1, α)` -/

/-- O6, closure form (Lin 2003, Lemma 5.8, as used at tex lines 1012--1014): below a
neutral wavenumber `α`, a limit in `(1, α)` of unstable wavenumbers is unstable. Real
limiting speeds, including an endpoint critical layer `c_∞ = Ω(±N)`, are excluded by
`ComplexODEB.noRealLimitSpeed_of_neutral`. -/
theorem closure_annularUnstable_inter_Ioo_subset {N α : ℝ} (hN : neutralCriticalTime < N)
    (hneut : neutralEvansFunction α (-N) N = 0) :
    closure (annularUnstable N) ∩ Ioo 1 α ⊆ annularUnstable N := by
  have hcrit := neutralCriticalTime_mem_Ioo_neg hN
  have hab : -N < N := hcrit.1.trans hcrit.2
  have hreal := ComplexODEB.noRealLimitSpeed_of_neutral hcrit
    ((ComplexODEB.neutralEvansFunction_eq_zero_iff α (-N) N).mp hneut)
  rintro β ⟨hcl, hβ⟩
  have hcl' : β ∈ closure (ComplexODEB.unstableWavenumbers (-N) N) := by
    refine closure_mono ?_ hcl
    rw [annularUnstable_eq]
    exact inter_subset_right
  rw [annularUnstable_eq]
  exact ⟨hβ.1, ComplexODEB.closure_inter_subset_unstable hab hreal ⟨hcl', hβ⟩⟩

/-- O6 (scoping `annularUnstable_relClosed`): the unstable wavenumbers are relatively
closed in `(1, α)` when `α` is a neutral wavenumber of `[-N, N]` and `t_* < N`. -/
theorem annularUnstable_relClosed {N α : ℝ} (hN : neutralCriticalTime < N)
    (hneut : neutralEvansFunction α (-N) N = 0) :
    IsClosed (Ioo 1 α ↓∩ annularUnstable N) := by
  rw [isClosed_preimage_val]
  rintro β ⟨hβ, hcl⟩
  exact closure_annularUnstable_inter_Ioo_subset hN hneut
    ⟨closure_mono inter_subset_right hcl, hβ⟩

/-! ### O7: the mode at `β = 2` on every large annulus -/

/-- Lin's continuation (tex lines 1012--1014): openness, relative closedness and the
bifurcation below `α` make every `β ∈ (1, α)` unstable. -/
theorem Ioo_subset_annularUnstable {N α : ℝ} (hN : neutralCriticalTime < N) (hα : 1 < α)
    (hneut : neutralEvansFunction α (-N) N = 0) : Ioo 1 α ⊆ annularUnstable N := by
  have hcrit := neutralCriticalTime_mem_Ioo_neg hN
  have hab : -N < N := hcrit.1.trans hcrit.2
  have hα' := (ComplexODEB.neutralEvansFunction_eq_zero_iff α (-N) N).mp hneut
  have h := ComplexODEB.Ioo_subset_unstableWavenumbers hab hα
    (ComplexODEB.bifurcatesBelow_of_neutral hα hcrit hα')
    (ComplexODEB.noRealLimitSpeed_of_neutral hcrit hα')
  intro β hβ
  rw [annularUnstable_eq]
  exact ⟨hβ.1, h hβ⟩

/-- An upper-half-plane zero of the angular-two Evans function on `[-N, N]` gives a
normalized annular mode (tex eq. `st18-t00033`, lines 1015--1021). -/
theorem exists_normalized_annularMode_of_evans_zero {N : ℝ} (hN : 0 < N) {c : ℂ}
    (hc : 0 < c.im) (he : evansFunction 2 (-N) N c = 0) :
    ∃ F : ℝ → ℂ, GaussianAnnularMode c F (-N) N ∧ (∫ t in Ioc (-N) N, ‖F t‖ ^ 2) = 1 := by
  have hab : -N < N := by linarith
  have hmode := gaussianAnnularMode_of_evans_zero hab hc he
  have hnz := normalizedF_nonzero_on_interval 2 hab hc
  exact ⟨_, hmode.normalized_is_mode, hmode.normalized_mass_one hab hnz⟩

/-- O7 (blueprint B0034, tex lines 1012--1021, eq. `st18-t00033`; scoping
`exists_annular_mode_two`): for every sufficiently large `N` the log-annulus `[-N, N]`
carries a normalized unstable Gaussian Rayleigh mode at angular index two. The neutral
wavenumber is O1's `α_N > 2`. -/
theorem exists_annular_mode_two : ∀ᶠ N : ℝ in atTop, ∃ (c : ℂ) (F : ℝ → ℂ),
    GaussianAnnularMode c F (-N) N ∧ (∫ t in Ioc (-N) N, ‖F t‖ ^ 2) = 1 := by
  filter_upwards [exists_dirichlet_neutral, eventually_gt_atTop neutralCriticalTime]
    with N hN hNt
  obtain ⟨αN, hα2, hneut, -, -, -⟩ := hN
  have hN0 : 0 < N := lt_trans neutralCriticalTime_pos hNt
  obtain ⟨-, c, hc, he⟩ :=
    Ioo_subset_annularUnstable hNt (by linarith) hneut ⟨by norm_num, hα2⟩
  obtain ⟨F, hF, hm⟩ := exists_normalized_annularMode_of_evans_zero hN0 hc he
  exact ⟨c, F, hF, hm⟩

/-! ### O8: the whole-line mode -/

/-- O8 (tex lines 1022--1121, §§`sec:st18-1192`--`sec:st18-1257`, eq. `st18-t00042`;
scoping `exists_wholeLine_growing_mode`): the logarithmic Gaussian Rayleigh equation at
angular index two, `(Ω - c)(F'' - 4F) - AF = 0`, has a classical whole-line solution
`F ≢ 0` with `F, F', F'' ∈ L²(ℝ)` at a speed `c` with `Im c > 0` and `0 < Re c < 1` in the
closed semicircle disc; `F` is smooth, has unit mass, and `F`, `F'` decay at both ends. -/
theorem exists_wholeLine_growing_mode : ∃ c : ℂ, 0 < c.im ∧ 0 < c.re ∧ c.re < 1 ∧
    (c.re - 1 / 2) ^ 2 + c.im ^ 2 ≤ 1 / 4 ∧
    ∃ F : ℝ → ℂ, GaussianWholeLineMode c F ∧ (∫ t, ‖F t‖ ^ 2) = 1 ∧ ContDiff ℝ ∞ F ∧
      Tendsto F atTop (𝓝 0) ∧ Tendsto F atBot (𝓝 0) ∧
      Tendsto (deriv F) atTop (𝓝 0) ∧ Tendsto (deriv F) atBot (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp exists_annular_mode_two
  have hseq : ∀ n : ℕ, ∃ (c : ℂ) (F : ℝ → ℂ),
      GaussianAnnularMode c F (-(N₀ + n)) (N₀ + n) ∧
        (∫ t in Ioc (-(N₀ + n)) (N₀ + n), ‖F t‖ ^ 2) = 1 := fun n =>
    hN₀ (N₀ + n) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  choose c F hmode hmass using hseq
  have hr : Tendsto (fun n : ℕ => N₀ + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop N₀ tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => -(N₀ + (n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hr
  obtain ⟨s, G, hG, hm, hsm, hcirc, hre0, hre1, h1, h2, h3, h4⟩ :=
    ComplexODEB.exists_normalized_wholeLineMode_of_annular_sequence c F
      (fun n => -(N₀ + (n : ℝ))) (fun n => N₀ + (n : ℝ)) hmode hmass hl hr
  exact ⟨s, hG.upper_half_plane, hre0, hre1, hcirc, G, hG, hm, hsm, h1, h2, h3, h4⟩

/-- Tex eq. `st18-t00042`: the growth rate `λ = -2ic = γ + iω` of the whole-line mode has
`γ > 0` and `-2 < ω < 0`. -/
theorem growthRate_bounds {c : ℂ} (him : 0 < c.im) (hre0 : 0 < c.re) (hre1 : c.re < 1) :
    0 < (-2 * Complex.I * c).re ∧ -2 < (-2 * Complex.I * c).im ∧ (-2 * Complex.I * c).im < 0 := by
  have hre : (-2 * Complex.I * c).re = 2 * c.im := by simp [Complex.mul_re, Complex.mul_im]
  have him' : (-2 * Complex.I * c).im = -2 * c.re := by simp [Complex.mul_re, Complex.mul_im]
  rw [hre, him']
  refine ⟨by linarith, by linarith, by linarith⟩

end UnforcedLeray.Rayleigh.Evans
