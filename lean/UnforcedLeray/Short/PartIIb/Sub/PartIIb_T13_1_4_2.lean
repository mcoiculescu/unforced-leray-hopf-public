import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4

/-!
# Part II-b, task `PartII-b:T13/1/4/2` (`ChmPeriodic`): decomposition

Source `the November 2 reference manuscript` (SP) lines 1933-1935 ("applying the
Euclidean estimate to a cutoff of `N` repeated cells, dividing its `r`-th power by `N`, and letting
`N → ∞`"), Euclidean estimate SP 1377-1424.

Fix a nice `q`-periodic `w`. For `N ≥ 1` take a cutoff `ζ = ζ_N(q)` equal to `1` on `[0, N c]`,
vanishing outside `[-c, (N+1)c]`, with `|ζ'| ≤ K/c`, `|ζ''| ≤ K/c²`. Then `U = ζ w` solves the heat
equation with right side `F = ζ chmRhs w - ν(2 ζ' ∂_q w + ζ'' w)` (`ChmLeibniz`). The Euclidean
estimate gives weak derivatives of `U`, which are the classical ones (`ChmWeakEq`), equal to those of
`w` on the core `q ∈ (0, N c)` (`ChmCoreDeriv`). By periodicity the volume norm over `N` cells is
`(N c)^{1/r}` times the cell norm (`ChmWindowLower`, `ChmWindowUpper`), the commutator lives on two
cells and is bounded independently of `N` (`ChmCommBound`). Dividing by `(N c)^{1/r}` and letting
`N → ∞` gives the a priori inequality with the Euclidean constant (proved here: `chm_limit_arith`,
`chmPeriodic_of`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The cutoff `ζ_N` of `N` cells: smooth, `0 ≤ ζ ≤ 1`, `ζ = 1` on `[0, N c]`, `ζ = 0` outside
`[-c, (N+1) c]`, `|ζ'| ≤ K/c`, `|ζ''| ≤ K/c²`. -/
def IsChmCut (K c : ℝ) (N : ℕ) (ζ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ Icc (0 : ℝ) ((N : ℝ) * c), ζ x = 1) ∧
    (∀ x, (x < -c ∨ ((N : ℝ) + 1) * c < x) → ζ x = 0) ∧ (∀ x, |deriv ζ x| ≤ K / c) ∧
    (∀ x, |deriv (deriv ζ) x| ≤ K / c ^ 2)

/-- The cut-off function `ζ(q) w(s,q,η)`. -/
def chmU (ζ : ℝ → ℝ) (w : Coord → ℂ) (x : Coord) : ℂ := (ζ x.2.1 : ℂ) * w x

/-- The commutator `ν(2 ζ' ∂_q w + ζ'' w)`. -/
def chmComm (ν : ℝ) (ζ : ℝ → ℝ) (w : Coord → ℂ) (x : Coord) : ℂ :=
  (ν : ℂ) * (2 * ((deriv ζ x.2.1 : ℝ) : ℂ) * cdv 1 w x + ((deriv (deriv ζ) x.2.1 : ℝ) : ℂ) * w x)

/-- The right-hand side `ζ chmRhs w - ν(2 ζ' ∂_q w + ζ'' w)` of the cut-off equation. -/
def chmF (ν : ℝ) (ζ : ℝ → ℝ) (w : Coord → ℂ) (x : Coord) : ℂ :=
  (ζ x.2.1 : ℂ) * chmRhs ν w x - chmComm ν ζ w x

/-- The core `q ∈ (0, N c)` where `ζ_N = 1`. -/
def chmCore (c : ℝ) (N : ℕ) : Set Coord := {x | x.2.1 ∈ Ioo (0 : ℝ) ((N : ℝ) * c)}

/-- **Lemma 1 (cutoff, SP 1933-1935).** A universal `K` for all `c > 0`, `N ≥ 1` (scale the
fixed profile `winCut1` of `FlatGraphOrg.lean`, or use a mollified indicator). -/
def ChmCutoffExists : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 0 < c → ∀ N : ℕ, 1 ≤ N → ∃ ζ : ℝ → ℝ, IsChmCut K c N ζ

/-- **Lemma 2 (Leibniz).** For smooth `w` and smooth `ζ` of bounded support,
`(∂_s - νΔ_{q,η})(ζ w) = chmF` in distributions (integrate by parts against test functions;
`ζ` depends on `q` only). -/
def ChmLeibniz : Prop :=
  ∀ (ν : ℝ) (w : Coord → ℂ) (ζ : ℝ → ℝ), ContDiff ℝ ∞ w → ContDiff ℝ ∞ ζ →
    (∃ a b : ℝ, ∀ t, (t < a ∨ b < t) → ζ t = 0) → IsCylHeat ν (chmU ζ w) (chmF ν ζ w)

/-- **Lemma 3 (upper window bound).** For `g` measurable and `q`-periodic and a bounded measurable
profile `h(q)` supported in `m` cells `[a, a + m c]`: `‖h g‖_{L^r(volume)} ≤ b (m c)^{1/r}
‖g‖_{L^r(cylMeas c)}` (the `volume` integral over `m` cells is `m c` times the `cylMeas` one,
`cylMeas = ds × (dq/c on a cell) × dη`; periodic strip decomposition). -/
def ChmWindowUpper : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ g : Coord → ℂ, AEStronglyMeasurable g volume →
    QPeriodicS c g → ∀ (h : ℝ → ℝ) (b a : ℝ) (m : ℕ), Measurable h → (∀ t, |h t| ≤ b) →
      (∀ t, (t < a ∨ a + (m : ℝ) * c < t) → h t = 0) →
      eLpNorm (fun x : Coord => (h x.2.1 : ℂ) * g x) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal (b * ((m : ℝ) * c) ^ (1 / r)) * cylNorm c r g

/-- **Lemma 4 (lower window bound).** If `G = g` a.e. on the core `q ∈ (0, N c)`, `g` periodic and
measurable, then `(N c)^{1/r} ‖g‖_{L^r(cylMeas c)} ≤ ‖G‖_{L^r(volume)}` (same strip identity). -/
def ChmWindowLower : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ (N : ℕ) (g G : Coord → ℂ), AEStronglyMeasurable g volume →
    QPeriodicS c g → AEStronglyMeasurable G volume →
    (∀ᵐ x ∂(volume.restrict (chmCore c N)), G x = g x) →
    ENNReal.ofReal (((N : ℝ) * c) ^ (1 / r)) * cylNorm c r g ≤
      eLpNorm G (ENNReal.ofReal r) volume

/-- **Lemma 5 (commutator).** `‖ν(2 ζ' ∂_q w + ζ'' w)‖_{L^r(volume)} ≤ M` with `M` independent of
`N`: it lives on the two cells `[-c, 0]`, `[N c, (N+1) c]` (`ζ'`, `ζ''` vanish on `(0, N c)`), where
`|ζ'| ≤ K/c`, `|ζ''| ≤ K/c²`, and `w, ∂_q w` have finite cell norms (periodicity, ChmNice). -/
def ChmCommBound : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c ν K : ℝ, 0 < c → 0 < ν → ∀ w : Coord → ℂ, ChmNice c r w →
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ N : ℕ, 1 ≤ N → ∀ ζ : ℝ → ℝ, IsChmCut K c N ζ →
      eLpNorm (chmComm ν ζ w) (ENNReal.ofReal r) volume ≤ M

/-- **Lemma 6 (weak derivatives of a smooth function are classical).** For smooth `u` and
`L^r` data `g` (resp. `ν g`), the weak identities give `g = ∂_s u` (resp. `g = ∂_i∂_j u`) a.e. -/
def ChmWeakEq : Prop :=
  ∀ r : ℝ, 1 < r → ∀ u : Coord → ℂ, ContDiff ℝ ∞ u →
    (∀ g : Coord → ℂ, AEStronglyMeasurable g volume →
      eLpNorm g (ENNReal.ofReal r) volume < ⊤ →
      (∀ φ, IsSTTestCoord φ → ∫ x, u x * (cpd 0 φ x : ℂ) = -∫ x, g x * (φ x : ℂ)) →
      g =ᵐ[volume] cdv 0 u) ∧
    (∀ (ν : ℝ), 0 < ν → ∀ (i j : Fin 2) (g : Coord → ℂ), AEStronglyMeasurable g volume →
      eLpNorm (fun x => (ν : ℂ) * g x) (ENNReal.ofReal r) volume < ⊤ →
      (∀ φ : Coord → ℝ, IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, g x * (φ x : ℂ)) →
      g =ᵐ[volume] cdv i.succ (cdv j.succ u))

/-- **Lemma 7 (derivatives on the core).** On `q ∈ (0, N c)` one has `ζ = 1`, `ζ' = ζ'' = 0`, so
`∂_s (ζ w) = ∂_s w` and `∂_i∂_j (ζ w) = ∂_i∂_j w` there (pure calculus). -/
def ChmCoreDeriv : Prop :=
  ∀ (K c : ℝ) (N : ℕ), 1 ≤ N → ∀ ζ : ℝ → ℝ, IsChmCut K c N ζ → ∀ w : Coord → ℂ,
    ContDiff ℝ ∞ w → ∀ x ∈ chmCore c N, cdv 0 (chmU ζ w) x = cdv 0 w x ∧
      ∀ i j : Fin 2, cdv i.succ (cdv j.succ (chmU ζ w)) x = cdv i.succ (cdv j.succ w) x

/-! ## Proved helpers -/

lemma chm_measurable_cdv (j : Fin 3) (w : Coord → ℂ) : Measurable (cdv j w) := by
  unfold cdv
  exact (measurable_fderiv ℝ w).apply_continuousLinearMap _

lemma chm_cdv_periodic (c : ℝ) (w : Coord → ℂ) (hw : ∀ x, w (qShift c x) = w x) (j : Fin 3) :
    ∀ x, cdv j w (qShift c x) = cdv j w x := by
  intro x
  have hq : ∀ y, qShift c y = y + (0, (c, 0)) := by
    intro y; simp [qShift, Prod.ext_iff]
  have h1 : (fun y => w (y + (0, (c, 0)))) = w := by
    funext y; rw [← hq]; exact hw y
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := w) (0, (c, 0)) (x := x)
  rw [h1] at h2
  unfold cdv
  rw [hq x, ← h2]

lemma chm_rhs_periodic (c ν : ℝ) (w : Coord → ℂ) (hw : ∀ x, w (qShift c x) = w x) :
    ∀ x, chmRhs ν w (qShift c x) = chmRhs ν w x := by
  intro x
  have h0 := chm_cdv_periodic c w hw
  have h1 := chm_cdv_periodic c (cdv 1 w) (h0 1)
  have h2 := chm_cdv_periodic c (cdv 2 w) (h0 2)
  unfold chmRhs
  rw [h0 0 x, h1 1 x, h2 2 x]

lemma chm_measurable_rhs (ν : ℝ) (w : Coord → ℂ) : Measurable (chmRhs ν w) := by
  unfold chmRhs
  exact (chm_measurable_cdv 0 w).sub (measurable_const.mul
    ((chm_measurable_cdv 1 _).add (chm_measurable_cdv 2 _)))

lemma chm_measurable_comm (ν : ℝ) (ζ : ℝ → ℝ) (w : Coord → ℂ) (hw : Measurable w) :
    Measurable (chmComm ν ζ w) := by
  unfold chmComm
  have h1 : Measurable fun x : Coord => ((deriv ζ x.2.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_deriv ζ).comp (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun x : Coord => ((deriv (deriv ζ) x.2.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp
      ((measurable_deriv (deriv ζ)).comp (measurable_fst.comp measurable_snd))
  exact measurable_const.mul ((measurable_const.mul h1).mul (chm_measurable_cdv 1 w) |>.add
    (h2.mul hw))

lemma chm_measurable_U (ζ : ℝ → ℝ) (hζ : Continuous ζ) (w : Coord → ℂ) (hw : Measurable w) :
    Measurable (chmU ζ w) := by
  unfold chmU
  exact (Complex.measurable_ofReal.comp
    (hζ.measurable.comp (measurable_fst.comp measurable_snd))).mul hw

lemma chm_measurable_F (ν : ℝ) (ζ : ℝ → ℝ) (hζ : Continuous ζ) (w : Coord → ℂ)
    (hw : Measurable w) : Measurable (chmF ν ζ w) := by
  unfold chmF
  exact ((Complex.measurable_ofReal.comp
    (hζ.measurable.comp (measurable_fst.comp measurable_snd))).mul
      (chm_measurable_rhs ν w)).sub (chm_measurable_comm ν ζ w hw)


/-- Real-number limit: `a_N x ≤ C0 (b_N R + m)` for all `N ≥ 1` gives `x ≤ C0 R`. -/
lemma chm_limit_real (r c C0 x R m : ℝ) (hr : 1 < r) (hc : 0 < c) (hx : 0 ≤ x) (hR : 0 ≤ R)
    (hm : 0 ≤ m) (hC : 0 < C0)
    (h : ∀ N : ℕ, 1 ≤ N → ((N : ℝ) * c) ^ (1 / r) * x ≤
      C0 * ((((N : ℝ) + 2) * c) ^ (1 / r) * R + m)) : x ≤ C0 * R := by
  have hr0 : 0 < 1 / r := by positivity
  have hA : Tendsto (fun N : ℕ => (((N : ℝ) * c) ^ (1 / r))) atTop atTop :=
    (tendsto_rpow_atTop hr0).comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
  have hB : Tendsto (fun N : ℕ => ((((N : ℝ) + 2) * c) ^ (1 / r)) / (((N : ℝ) * c) ^ (1 / r)))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (1 + 2 / (N : ℝ)) ^ (1 / r)) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))).rpow_const (p := 1 / r) (Or.inr hr0.le)
      simpa using this
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hD : Tendsto (fun N : ℕ => m / (((N : ℝ) * c) ^ (1 / r))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hA
  have hL := ((hB.mul_const R).add hD).const_mul C0
  have hev : ∀ᶠ N : ℕ in atTop, x ≤ C0 * ((((((N : ℝ) + 2) * c) ^ (1 / r)) /
      (((N : ℝ) * c) ^ (1 / r))) * R + m / (((N : ℝ) * c) ^ (1 / r))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have ha : 0 < ((N : ℝ) * c) ^ (1 / r) := Real.rpow_pos_of_pos (by positivity) _
    have e : C0 * ((((((N : ℝ) + 2) * c) ^ (1 / r)) / (((N : ℝ) * c) ^ (1 / r))) * R +
        m / (((N : ℝ) * c) ^ (1 / r))) =
        C0 * ((((N : ℝ) + 2) * c) ^ (1 / r) * R + m) / (((N : ℝ) * c) ^ (1 / r)) := by
      field_simp
    rw [e, le_div_iff₀ ha]
    linarith [h N hN]
  have := ge_of_tendsto hL hev
  simpa using this

/-- ENNReal form of the limit. -/
lemma chm_limit_arith (r c C0 : ℝ) (hr : 1 < r) (hc : 0 < c) (hC : 0 < C0) (X R M : ℝ≥0∞)
    (hM : M < ⊤)
    (h : ∀ N : ℕ, 1 ≤ N → ENNReal.ofReal (((N : ℝ) * c) ^ (1 / r)) * X ≤
      ENNReal.ofReal C0 * (ENNReal.ofReal ((((N : ℝ) + 2) * c) ^ (1 / r)) * R + M)) :
    X ≤ ENNReal.ofReal C0 * R := by
  by_cases hR : R = ⊤
  · rw [hR, ENNReal.mul_top (by simpa using hC)]; exact le_top
  have hRt : R < ⊤ := lt_top_iff_ne_top.2 hR
  by_cases hX : X = ⊤
  · exfalso
    have h1 := h 1 le_rfl
    rw [hX, ENNReal.mul_top (by
      simp only [Nat.cast_one, one_mul]
      exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hc _)).ne')] at h1
    have : ENNReal.ofReal C0 * (ENNReal.ofReal (((((1:ℕ) : ℝ) + 2) * c) ^ (1 / r)) * R + M) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRt, hM⟩)
    exact absurd (top_le_iff.1 h1) this.ne
  have hMt : M ≠ ⊤ := hM.ne
  have key := chm_limit_real r c C0 X.toReal R.toReal M.toReal hr hc ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hC (by
      intro N hN
      have h' := h N hN
      have hfin : ENNReal.ofReal C0 * (ENNReal.ofReal ((((N : ℝ) + 2) * c) ^ (1 / r)) * R + M) ≠ ⊤ :=
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRt, hM⟩)).ne
      have := ENNReal.toReal_mono hfin h'
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hR) hMt, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hC.le,
        ENNReal.toReal_ofReal (by positivity)] at this
      exact this)
  have : X.toReal ≤ (ENNReal.ofReal C0 * R).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]; exact key
  exact (ENNReal.toReal_le_toReal hX (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hR)).1 this

/-- **`ChmPeriodic` from `ChmEuclid` and the seven lemmas** (cutoff of `N` cells, divide by
`(N c)^{1/r}`, `N → ∞`; SP 1933-1935). -/
theorem chmPeriodic_of (hE : ChmEuclid) (h1 : ChmCutoffExists) (h2 : ChmLeibniz)
    (h3 : ChmWindowUpper) (h4 : ChmWindowLower) (h5 : ChmCommBound) (h6 : ChmWeakEq)
    (h7 : ChmCoreDeriv) : ChmPeriodic := by
  intro r hr
  obtain ⟨C, hC, hEu⟩ := hE r hr
  obtain ⟨K, hK, hcut⟩ := h1
  refine ⟨C, hC, fun c ν hc hν w hw => ?_⟩
  by_cases hR : cylNorm c r (chmRhs ν w) = ⊤
  · rw [hR, ENNReal.mul_top (by simpa using hC)]
    exact ⟨le_top, fun _ _ => le_top⟩
  have hRt : cylNorm c r (chmRhs ν w) < ⊤ := lt_top_iff_ne_top.2 hR
  obtain ⟨M, hMt, hMb⟩ := h5 r hr c ν K hc hν w hw
  have hwc : Continuous w := hw.smooth.continuous
  have hwm : Measurable w := hwc.measurable
  have hper := chm_cdv_periodic c w hw.periodic
  have hper2 := fun a b => chm_cdv_periodic c (cdv b w) (hper b) a
  -- the key inequality for every `N ≥ 1`
  have key : ∀ N : ℕ, 1 ≤ N → ∃ (Dt : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
      ENNReal.ofReal (((N : ℝ) * c) ^ (1 / r)) * cylNorm c r (cdv 0 w) ≤ eLpNorm Dt (ENNReal.ofReal r) volume ∧
      (∀ i j, ENNReal.ofReal (((N : ℝ) * c) ^ (1 / r)) *
        cylNorm c r (fun x => (ν : ℂ) * cdv i.succ (cdv j.succ w) x) ≤
        eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) volume) ∧
      eLpNorm Dt (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C *
        (ENNReal.ofReal ((((N : ℝ) + 2) * c) ^ (1 / r)) * cylNorm c r (chmRhs ν w) + M) ∧
      (∀ i j, eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C *
        (ENNReal.ofReal ((((N : ℝ) + 2) * c) ^ (1 / r)) * cylNorm c r (chmRhs ν w) + M)) := by
    intro N hN
    obtain ⟨ζ, hζ⟩ := hcut c hc N hN
    have hζ' := hζ
    obtain ⟨hζs, hζ01, hζ1, hζ0, hζd1, hζd2⟩ := hζ'
    have hζc : Continuous ζ := hζs.continuous
    have hUm : Measurable (chmU ζ w) := chm_measurable_U ζ hζc w hwm
    have hFm : Measurable (chmF ν ζ w) := chm_measurable_F ν ζ hζc w hwm
    have hsupp : ∀ t, (t < -c ∨ -c + (((N + 2 : ℕ) : ℝ)) * c < t) → ζ t = 0 := by
      intro t ht
      apply hζ0 t
      push_cast at ht
      rcases ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr (by linarith)
    -- finiteness of `U`
    have hUn : eLpNorm (chmU ζ w) (ENNReal.ofReal r) volume < ⊤ := by
      have := h3 r hr c hc w hwm.aestronglyMeasurable
        (Filter.Eventually.of_forall hw.periodic) ζ 1 (-c) (N + 2) hζc.measurable
        (fun t => by rw [abs_le]; constructor <;> linarith [(hζ01 t).1, (hζ01 t).2])
        hsupp
      exact lt_of_le_of_lt this (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw.mem0)
    -- the bound for `F`
    have hFb : eLpNorm (chmF ν ζ w) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal ((((N : ℝ) + 2) * c) ^ (1 / r)) * cylNorm c r (chmRhs ν w) + M := by
      have hA := h3 r hr c hc (chmRhs ν w) (chm_measurable_rhs ν w).aestronglyMeasurable
        (Filter.Eventually.of_forall (chm_rhs_periodic c ν w hw.periodic)) ζ 1 (-c) (N + 2)
        hζc.measurable
        (fun t => by rw [abs_le]; constructor <;> linarith [(hζ01 t).1, (hζ01 t).2])
        hsupp
      have hB := hMb N hN ζ hζ
      have hsub := eLpNorm_sub_le (μ := volume) (p := ENNReal.ofReal r)
        (f := fun x : Coord => (ζ x.2.1 : ℂ) * chmRhs ν w x) (g := chmComm ν ζ w)
        (Measurable.aestronglyMeasurable (Complex.measurable_ofReal.comp
          (hζc.measurable.comp (measurable_fst.comp measurable_snd)) |>.mul
            (chm_measurable_rhs ν w)))
        (chm_measurable_comm ν ζ w hwm).aestronglyMeasurable
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le)
      refine hsub.trans (add_le_add ?_ hB)
      simpa [one_mul, Nat.cast_add, Nat.cast_ofNat] using hA
    have hFn : eLpNorm (chmF ν ζ w) (ENNReal.ofReal r) volume < ⊤ :=
      lt_of_le_of_lt hFb (ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRt, hMt⟩)
    have hheat := h2 ν w ζ hw.smooth hζs ⟨-c, ((N : ℝ) + 1) * c, fun t ht => hζ0 t ht⟩
    obtain ⟨Dt, D2, hDtm, hD2m, hDtw, hD2w, hDtn, hD2n⟩ :=
      hEu ν hν (chmU ζ w) (chmF ν ζ w) hUm.aestronglyMeasurable hFm.aestronglyMeasurable
        hUn hFn hheat
    have hUs : ContDiff ℝ ∞ (chmU ζ w) := by
      unfold chmU
      exact (Complex.ofRealCLM.contDiff.comp
        (hζs.comp (contDiff_fst.comp contDiff_snd))).mul hw.smooth
    obtain ⟨hW1, hW2⟩ := h6 r hr (chmU ζ w) hUs
    have hDt_fin : eLpNorm Dt (ENNReal.ofReal r) volume < ⊤ :=
      lt_of_le_of_lt hDtn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFn)
    have hDt_eq := hW1 Dt hDtm hDt_fin hDtw
    have hcore := h7 K c N hN ζ hζ w hw.smooth
    have hmeas_core : MeasurableSet (chmCore c N) := by
      unfold chmCore
      exact measurableSet_Ioo.preimage (measurable_fst.comp measurable_snd)
    refine ⟨Dt, D2, ?_, ?_, ?_, ?_⟩
    · refine h4 r hr c hc N (cdv 0 w) Dt (chm_measurable_cdv 0 w).aestronglyMeasurable
        (Filter.Eventually.of_forall (hper 0)) hDtm ?_
      filter_upwards [ae_restrict_of_ae hDt_eq, ae_restrict_mem hmeas_core] with x h hx
      rw [h]; exact (hcore x hx).1
    · intro i j
      have hfin : eLpNorm (fun x => (ν : ℂ) * D2 i j x) (ENNReal.ofReal r) volume < ⊤ :=
        lt_of_le_of_lt (hD2n i j) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFn)
      have hD2_eq := hW2 ν hν i j (D2 i j) (hD2m i j) hfin (hD2w i j)
      refine h4 r hr c hc N (fun x => (ν : ℂ) * cdv i.succ (cdv j.succ w) x) _
        (measurable_const.mul (chm_measurable_cdv _ _)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => by
          show (ν : ℂ) * cdv i.succ (cdv j.succ w) (qShift c x) = _
          rw [hper2 i.succ j.succ x]))
        ((hD2m i j).const_mul _) ?_
      filter_upwards [ae_restrict_of_ae hD2_eq, ae_restrict_mem hmeas_core] with x h hx
      show (ν : ℂ) * D2 i j x = _
      rw [h]; exact congrArg _ ((hcore x hx).2 i j)
    · exact hDtn.trans (by gcongr)
    · intro i j
      exact (hD2n i j).trans (by gcongr)
  refine ⟨?_, fun i j => ?_⟩
  · refine chm_limit_arith r c C hr hc hC _ _ M hMt (fun N hN => ?_)
    obtain ⟨Dt, D2, a, b, c', d⟩ := key N hN
    exact a.trans c'
  · refine chm_limit_arith r c C hr hc hC _ _ M hMt (fun N hN => ?_)
    obtain ⟨Dt, D2, a, b, c', d⟩ := key N hN
    exact (b i j).trans (d i j)

end UnforcedLeray.Short.IIb
