import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus.Closure

/-!
# Helper for `PartII-a:R01`, target `earlyCalculus`: multiplication by `η` and by `s`

Helpers for `Tasks/R01/EarlyCalculus.lean`: `EarlyBdd` is closed under `(η, s) ↦ η·X, s·X`.
The coordinate functions `η` and `s` have `∂_η η = 1`, `∂_s s = 1` and vanish under the other
two directional derivatives, so the Leibniz rule for these multiplications has at most one
correction term; the age factor `s ≤ 1` on `0 < s ≤ 1` absorbs the `s`-weight, while the
`η`-weight is absorbed by raising the weight `(1+η²)^m` to `(1+η²)^{m+1}` (`|η| ≤ 1+η²`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.EarlyCalc

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

theorem smooth_eta_fun : ContDiffOn ℝ ∞ (fun y : ProfilePoint => y.2.1) AgeSet :=
  (contDiff_fst.comp contDiff_snd).contDiffOn

theorem smooth_age_fun : ContDiffOn ℝ ∞ (fun y : ProfilePoint => y.2.2) AgeSet :=
  (contDiff_snd.comp contDiff_snd).contDiffOn

theorem Dir_eta_val (v x : ProfilePoint) : Dir v (fun y => y.2.1) x = v.2.1 := by
  simp only [Dir]
  rw [(hasFDerivAt_eta x).fderiv]
  rfl

theorem Dir_age_val (v x : ProfilePoint) : Dir v (fun y => y.2.2) x = v.2.2 := by
  simp only [Dir]
  rw [(hasFDerivAt_age x).fderiv]
  rfl

theorem Dir_eta_q (x : ProfilePoint) : Dir eqDir (fun y => y.2.1) x = 0 := by
  rw [Dir_eta_val]
  rfl

theorem Dir_eta_s (x : ProfilePoint) : Dir esDir (fun y => y.2.1) x = 0 := by
  rw [Dir_eta_val]
  rfl

theorem Dir_eta_eta (x : ProfilePoint) : Dir eηDir (fun y => y.2.1) x = 1 := by
  rw [Dir_eta_val]
  rfl

theorem Dir_age_q (x : ProfilePoint) : Dir eqDir (fun y => y.2.2) x = 0 := by
  rw [Dir_age_val]
  rfl

theorem Dir_age_eta (x : ProfilePoint) : Dir eηDir (fun y => y.2.2) x = 0 := by
  rw [Dir_age_val]
  rfl

theorem Dir_age_s (x : ProfilePoint) : Dir esDir (fun y => y.2.2) x = 1 := by
  rw [Dir_age_val]
  rfl

/-- Multiplication by a function `K` with `Dir v K = 0` commutes with `(Dir v)^[n]`. -/
theorem iter_mul_zero_dir (v : ProfilePoint) (K : ProfilePoint → ℝ)
    (hK : ContDiffOn ℝ ∞ K AgeSet) (hv : ∀ x ∈ AgeSet, Dir v K x = 0) (n : ℕ)
    {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G AgeSet) :
    EqOn ((Dir v)^[n] (fun y => K y * G y)) (fun y => K y * (Dir v)^[n] G y) AgeSet := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    simp only [Function.iterate_succ_apply']
    rw [Dir_congr v ih hx, Dir_mul v hK (smooth_iter v n hG) hx, hv x hx]
    ring

/-- The Leibniz rule for `(Dir w)^[n+1]` applied to `K · G`, where `Dir w K = 1`. -/
theorem iter_mul_lin (w : ProfilePoint) (K : ProfilePoint → ℝ) (hK : ContDiffOn ℝ ∞ K AgeSet)
    (hK1 : ∀ x ∈ AgeSet, Dir w K x = 1) (n : ℕ) {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G AgeSet) :
    EqOn ((Dir w)^[n + 1] (fun y => K y * G y))
      (fun y => K y * (Dir w)^[n + 1] G y + ((n : ℝ) + 1) * (Dir w)^[n] G y) AgeSet := by
  induction n with
  | zero =>
    intro x hx
    simp only [Function.iterate_one, Function.iterate_zero, id_eq, Nat.cast_zero, zero_add,
      one_mul]
    rw [Dir_mul w hK hG hx, hK1 x hx]
    ring
  | succ n ih =>
    intro x hx
    have hA : ContDiffOn ℝ ∞ (fun y => K y * (Dir w)^[n + 1] G y) AgeSet :=
      hK.mul (smooth_iter w (n + 1) hG)
    have hB : ContDiffOn ℝ ∞ (fun y => ((n : ℝ) + 1) * (Dir w)^[n] G y) AgeSet :=
      contDiffOn_const.mul (smooth_iter w n hG)
    rw [Function.iterate_succ_apply' (Dir w) (n + 1) (fun y => K y * G y), Dir_congr w ih hx,
      Dir_add w hA hB hx, Dir_mul w hK (smooth_iter w (n + 1) hG) hx,
      Dir_const_mul w _ (smooth_iter w n hG) hx, hK1 x hx]
    simp only [Function.iterate_succ_apply']
    push_cast
    ring

/-! ### Jets of `η·G` and `s·G` -/

theorem jet_eta_zero (ℓ b : ℕ) {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet ℓ 0 b (fun y => y.2.1 * G y) x = x.2.1 * jet ℓ 0 b G x := by
  have e1 := iter_mul_zero_dir eqDir (fun y => y.2.1) smooth_eta_fun
    (fun x _ => Dir_eta_q x) b hG
  have e2 := iter_mul_zero_dir esDir (fun y => y.2.1) smooth_eta_fun
    (fun x _ => Dir_eta_s x) ℓ (smooth_iter eqDir b hG)
  have e3 := iter_congr esDir ℓ e1
  exact (e3.trans e2) hx

theorem jet_eta_succ (ℓ a b : ℕ) {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet ℓ (a + 1) b (fun y => y.2.1 * G y) x =
      x.2.1 * jet ℓ (a + 1) b G x + ((a : ℝ) + 1) * jet ℓ a b G x := by
  have hG1 := smooth_iter eqDir b hG
  have e1 := iter_mul_zero_dir eqDir (fun y => y.2.1) smooth_eta_fun
    (fun x _ => Dir_eta_q x) b hG
  have e2 := iter_mul_lin eηDir (fun y => y.2.1) smooth_eta_fun
    (fun x _ => Dir_eta_eta x) a hG1
  have e3 := iter_congr eηDir (a + 1) e1
  have hH1 := smooth_iter eηDir (a + 1) hG1
  have hH0 := smooth_iter eηDir a hG1
  have hA : ContDiffOn ℝ ∞ (fun y => y.2.1 * (Dir eηDir)^[a + 1] ((Dir eqDir)^[b] G) y) AgeSet :=
    smooth_eta_fun.mul hH1
  have hB : ContDiffOn ℝ ∞ (fun y => ((a : ℝ) + 1) * (Dir eηDir)^[a] ((Dir eqDir)^[b] G) y)
      AgeSet := contDiffOn_const.mul hH0
  have e4 := iter_congr esDir ℓ (e3.trans e2)
  have e5 := iter_add esDir ℓ hA hB
  have e6 := iter_mul_zero_dir esDir (fun y => y.2.1) smooth_eta_fun
    (fun x _ => Dir_eta_s x) ℓ hH1
  have e7 := iter_const esDir ℓ ((a : ℝ) + 1) hH0
  have h1 := (e4.trans e5) hx
  have h2 := e6 hx
  have h3 := e7 hx
  dsimp only at h1 h2 h3
  show (Dir esDir)^[ℓ] ((Dir eηDir)^[a + 1] ((Dir eqDir)^[b] (fun y => y.2.1 * G y))) x = _
  rw [h1, h2, h3]
  rfl

theorem jet_age_zero (a b : ℕ) {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet 0 a b (fun y => y.2.2 * G y) x = x.2.2 * jet 0 a b G x := by
  have f1 := iter_mul_zero_dir eqDir (fun y => y.2.2) smooth_age_fun
    (fun x _ => Dir_age_q x) b hG
  have f2 := iter_congr eηDir a f1
  have f3 := iter_mul_zero_dir eηDir (fun y => y.2.2) smooth_age_fun
    (fun x _ => Dir_age_eta x) a (smooth_iter eqDir b hG)
  exact (f2.trans f3) hx

theorem jet_age_succ (ℓ a b : ℕ) {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G AgeSet)
    {x : ProfilePoint} (hx : x ∈ AgeSet) :
    jet (ℓ + 1) a b (fun y => y.2.2 * G y) x =
      x.2.2 * jet (ℓ + 1) a b G x + ((ℓ : ℝ) + 1) * jet ℓ a b G x := by
  have hG1 := smooth_iter eqDir b hG
  have f1 := iter_mul_zero_dir eqDir (fun y => y.2.2) smooth_age_fun
    (fun x _ => Dir_age_q x) b hG
  have f2 := iter_congr eηDir a f1
  have f3 := iter_mul_zero_dir eηDir (fun y => y.2.2) smooth_age_fun
    (fun x _ => Dir_age_eta x) a hG1
  have f4 := iter_congr esDir (ℓ + 1) (f2.trans f3)
  have hK := smooth_iter eηDir a hG1
  have f5 := iter_mul_lin esDir (fun y => y.2.2) smooth_age_fun
    (fun x _ => Dir_age_s x) ℓ hK
  have h1 := (f4.trans f5) hx
  dsimp only at h1
  show (Dir esDir)^[ℓ + 1] ((Dir eηDir)^[a] ((Dir eqDir)^[b] (fun y => y.2.2 * G y))) x = _
  exact h1

/-! ### Weighted inequalities -/

theorem abs_le_one_add_sq' (e : ℝ) : |e| ≤ 1 + e ^ 2 := by
  nlinarith [sq_abs e, sq_nonneg (|e| - 1), sq_nonneg e, abs_nonneg e]

theorem weight_single (m : ℕ) (e J : ℝ) :
    (1 + e ^ 2) ^ m * |e * J| ≤ (1 + e ^ 2) ^ (m + 1) * |J| := by
  have hw : 0 ≤ (1 + e ^ 2) ^ m := by positivity
  have h1 : (1 + e ^ 2) ^ m * |e| ≤ (1 + e ^ 2) ^ (m + 1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (abs_le_one_add_sq' e) hw
  rw [abs_mul]
  have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg J)
  linarith [show (1 + e ^ 2) ^ m * (|e| * |J|) = (1 + e ^ 2) ^ m * |e| * |J| by ring]

theorem weight_combo_eta (m : ℕ) (e J1 J0 k : ℝ) (hk : 0 ≤ k) :
    (1 + e ^ 2) ^ m * |e * J1 + k * J0| ≤
      (1 + e ^ 2) ^ (m + 1) * |J1| + k * ((1 + e ^ 2) ^ m * |J0|) := by
  have hw : 0 ≤ (1 + e ^ 2) ^ m := by positivity
  have h0 : |e * J1 + k * J0| ≤ |e| * |J1| + k * |J0| := by
    calc |e * J1 + k * J0| ≤ |e * J1| + |k * J0| := abs_add_le _ _
      _ = |e| * |J1| + k * |J0| := by rw [abs_mul, abs_mul, abs_of_nonneg hk]
  have h1 : (1 + e ^ 2) ^ m * |e| ≤ (1 + e ^ 2) ^ (m + 1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (abs_le_one_add_sq' e) hw
  have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg J1)
  calc (1 + e ^ 2) ^ m * |e * J1 + k * J0| ≤ (1 + e ^ 2) ^ m * (|e| * |J1| + k * |J0|) :=
        mul_le_mul_of_nonneg_left h0 hw
    _ = (1 + e ^ 2) ^ m * |e| * |J1| + k * ((1 + e ^ 2) ^ m * |J0|) := by ring
    _ ≤ (1 + e ^ 2) ^ (m + 1) * |J1| + k * ((1 + e ^ 2) ^ m * |J0|) := by linarith

theorem weight_combo_age (m : ℕ) (e s J1 J0 k : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hk : 0 ≤ k) :
    (1 + e ^ 2) ^ m * |s * J1 + k * J0| ≤
      (1 + e ^ 2) ^ m * |J1| + k * ((1 + e ^ 2) ^ m * |J0|) := by
  have hw : 0 ≤ (1 + e ^ 2) ^ m := by positivity
  have h0 : |s * J1 + k * J0| ≤ |J1| + k * |J0| := by
    calc |s * J1 + k * J0| ≤ |s * J1| + |k * J0| := abs_add_le _ _
      _ = s * |J1| + k * |J0| := by rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hk]
      _ ≤ |J1| + k * |J0| := by linarith [mul_le_of_le_one_left (abs_nonneg J1) hs1]
  calc (1 + e ^ 2) ^ m * |s * J1 + k * J0| ≤ (1 + e ^ 2) ^ m * (|J1| + k * |J0|) :=
        mul_le_mul_of_nonneg_left h0 hw
    _ = (1 + e ^ 2) ^ m * |J1| + k * ((1 + e ^ 2) ^ m * |J0|) := by ring

theorem polyConst_combo {C₁ C₂ k : ℝ} {d₁ d₂ : ℕ} {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hk : 0 ≤ k) :
    polyConst C₁ d₁ ν c + k * polyConst C₂ d₂ ν c ≤
      polyConst (max C₁ 0 + k * max C₂ 0) (max d₁ d₂) ν c := by
  have h1 : polyConst C₁ d₁ ν c ≤ polyConst (max C₁ 0) (max d₁ d₂) ν c :=
    polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
  have h2 : polyConst C₂ d₂ ν c ≤ polyConst (max C₂ 0) (max d₁ d₂) ν c :=
    polyConst_mono hν hc (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
  have h3 : k * polyConst C₂ d₂ ν c ≤ k * polyConst (max C₂ 0) (max d₁ d₂) ν c :=
    mul_le_mul_of_nonneg_left h2 hk
  have e : polyConst (max C₁ 0) (max d₁ d₂) ν c +
      k * polyConst (max C₂ 0) (max d₁ d₂) ν c =
      polyConst (max C₁ 0 + k * max C₂ 0) (max d₁ d₂) ν c := by
    unfold polyConst
    ring
  linarith

/-! ### Closure under multiplication by `η` and by `s` -/

theorem earlyBdd_etaMul {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p x => x.2.1 * X ν ψ p x) := by
  unfold EarlyBdd at h ⊢
  refine ⟨fun ν hν ψ p hψ => smooth_eta_fun.mul (h.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  rcases a with _ | a
  · obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 (m + 1) 0 b ℓ
    refine ⟨ν₀, max C 0, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
    have hν0 : 0 < ν := hν.1
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
    have t : (1 + x.2.1 ^ 2) ^ (m + 1) * |jet ℓ 0 b (X ν ψ p) x| ≤ polyConst C d ν (ν ^ (-ρ)) :=
      H ν hν ψ p hψ x hx0 hx1
    show (1 + x.2.1 ^ 2) ^ m * |jet ℓ 0 b (fun y => y.2.1 * X ν ψ p y) x| ≤ _
    rw [jet_eta_zero ℓ b (h.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
    calc (1 + x.2.1 ^ 2) ^ m * |x.2.1 * jet ℓ 0 b (X ν ψ p) x|
        ≤ (1 + x.2.1 ^ 2) ^ (m + 1) * |jet ℓ 0 b (X ν ψ p) x| := weight_single m _ _
      _ ≤ polyConst C d ν (ν ^ (-ρ)) := t
      _ ≤ polyConst (max C 0) d ν (ν ^ (-ρ)) :=
          polyConst_mono hν0 hc (le_max_left C 0) (le_max_right C 0) le_rfl
  · obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := h.2 (m + 1) (a + 1) b ℓ
    obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := h.2 m a b ℓ
    refine ⟨min ν₁ ν₂, max C₁ 0 + ((a : ℝ) + 1) * max C₂ 0, max d₁ d₂, lt_min hν₁ hν₂,
      fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
    have hν0 : 0 < ν := hν.1
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
    have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
    have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
    have t1 : (1 + x.2.1 ^ 2) ^ (m + 1) * |jet ℓ (a + 1) b (X ν ψ p) x| ≤
        polyConst C₁ d₁ ν (ν ^ (-ρ)) := H₁ ν hνX ψ p hψ x hx0 hx1
    have t2 : (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| ≤ polyConst C₂ d₂ ν (ν ^ (-ρ)) :=
      H₂ ν hνY ψ p hψ x hx0 hx1
    show (1 + x.2.1 ^ 2) ^ m * |jet ℓ (a + 1) b (fun y => y.2.1 * X ν ψ p y) x| ≤ _
    rw [jet_eta_succ ℓ a b (h.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
    have hk : (0 : ℝ) ≤ (a : ℝ) + 1 := by positivity
    calc (1 + x.2.1 ^ 2) ^ m * |x.2.1 * jet ℓ (a + 1) b (X ν ψ p) x + ((a : ℝ) + 1) *
          jet ℓ a b (X ν ψ p) x|
        ≤ (1 + x.2.1 ^ 2) ^ (m + 1) * |jet ℓ (a + 1) b (X ν ψ p) x| +
            ((a : ℝ) + 1) * ((1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x|) :=
          weight_combo_eta m _ _ _ _ hk
      _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) + ((a : ℝ) + 1) * polyConst C₂ d₂ ν (ν ^ (-ρ)) :=
          add_le_add t1 (mul_le_mul_of_nonneg_left t2 hk)
      _ ≤ _ := polyConst_combo hν0 hc hk

theorem earlyBdd_ageMul {ρ : ℝ} {X : ProfFam} (h : EarlyBdd ρ X) :
    EarlyBdd ρ (fun ν ψ p x => x.2.2 * X ν ψ p x) := by
  unfold EarlyBdd at h ⊢
  refine ⟨fun ν hν ψ p hψ => smooth_age_fun.mul (h.1 ν hν ψ p hψ), fun m a b ℓ => ?_⟩
  rcases ℓ with _ | ℓ
  · obtain ⟨ν₀, C, d, hν₀, H⟩ := h.2 m a b 0
    refine ⟨ν₀, max C 0, d, hν₀, fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
    have hν0 : 0 < ν := hν.1
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
    have t : (1 + x.2.1 ^ 2) ^ m * |jet 0 a b (X ν ψ p) x| ≤ polyConst C d ν (ν ^ (-ρ)) :=
      H ν hν ψ p hψ x hx0 hx1
    show (1 + x.2.1 ^ 2) ^ m * |jet 0 a b (fun y => y.2.2 * X ν ψ p y) x| ≤ _
    rw [jet_age_zero a b (h.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
    have hw : 0 ≤ (1 + x.2.1 ^ 2) ^ m := by positivity
    calc (1 + x.2.1 ^ 2) ^ m * |x.2.2 * jet 0 a b (X ν ψ p) x|
        = x.2.2 * ((1 + x.2.1 ^ 2) ^ m * |jet 0 a b (X ν ψ p) x|) := by
          rw [abs_mul, abs_of_pos hx0]
          ring
      _ ≤ 1 * ((1 + x.2.1 ^ 2) ^ m * |jet 0 a b (X ν ψ p) x|) :=
          mul_le_mul_of_nonneg_right hx1 (mul_nonneg hw (abs_nonneg _))
      _ ≤ polyConst C d ν (ν ^ (-ρ)) := by linarith
      _ ≤ polyConst (max C 0) d ν (ν ^ (-ρ)) :=
          polyConst_mono hν0 hc (le_max_left C 0) (le_max_right C 0) le_rfl
  · obtain ⟨ν₁, C₁, d₁, hν₁, H₁⟩ := h.2 m a b (ℓ + 1)
    obtain ⟨ν₂, C₂, d₂, hν₂, H₂⟩ := h.2 m a b ℓ
    refine ⟨min ν₁ ν₂, max C₁ 0 + ((ℓ : ℝ) + 1) * max C₂ 0, max d₁ d₂, lt_min hν₁ hν₂,
      fun ν hν ψ p hψ x hx0 hx1 => ?_⟩
    have hν0 : 0 < ν := hν.1
    have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
    have hνX : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
    have hνY : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
    have t1 : (1 + x.2.1 ^ 2) ^ m * |jet (ℓ + 1) a b (X ν ψ p) x| ≤
        polyConst C₁ d₁ ν (ν ^ (-ρ)) := H₁ ν hνX ψ p hψ x hx0 hx1
    have t2 : (1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x| ≤ polyConst C₂ d₂ ν (ν ^ (-ρ)) :=
      H₂ ν hνY ψ p hψ x hx0 hx1
    show (1 + x.2.1 ^ 2) ^ m * |jet (ℓ + 1) a b (fun y => y.2.2 * X ν ψ p y) x| ≤ _
    rw [jet_age_succ ℓ a b (h.1 ν hν0 ψ p hψ) (show x ∈ AgeSet from hx0)]
    have hk : (0 : ℝ) ≤ (ℓ : ℝ) + 1 := by positivity
    calc (1 + x.2.1 ^ 2) ^ m * |x.2.2 * jet (ℓ + 1) a b (X ν ψ p) x + ((ℓ : ℝ) + 1) *
          jet ℓ a b (X ν ψ p) x|
        ≤ (1 + x.2.1 ^ 2) ^ m * |jet (ℓ + 1) a b (X ν ψ p) x| +
            ((ℓ : ℝ) + 1) * ((1 + x.2.1 ^ 2) ^ m * |jet ℓ a b (X ν ψ p) x|) :=
          weight_combo_age m _ _ _ _ _ hx0.le hx1 hk
      _ ≤ polyConst C₁ d₁ ν (ν ^ (-ρ)) + ((ℓ : ℝ) + 1) * polyConst C₂ d₂ ν (ν ^ (-ρ)) :=
          add_le_add t1 (mul_le_mul_of_nonneg_left t2 hk)
      _ ≤ _ := polyConst_combo hν0 hc hk

end UnforcedLeray.Short.PartIIa.EarlyCalc
