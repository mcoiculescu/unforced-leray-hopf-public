import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_2.Calc2

/-!
# Conormal words of `b = h^p_A + εΘ` (task `PartIII-b:C/asrc/ra/9/1/2/8/2`)

Source `the November 2 reference manuscript` lines 5034-5039, 4979-4980:
`Θ = (0, (1 - 𝒦)ψ^p_A)`; the words of length `≤ 2` of `Θ` are words of length `≤ 3` of `ψ^p_A`
with `η`-weight `≤ 1 + |η|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Kc_fun_eq (F : Chart → E) :
    Kc F = ((2 : ℝ) • opW 0 F) + fun p : Chart => p.2.2 • opW 2 F p := by
  funext p; simp [Kc_eq]

theorem cd_etaE {n : ℕ} {F : Chart → E} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F UC) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : Chart => p.2.2 • opW 2 F p) UC :=
  (contDiff_snd.comp contDiff_snd).contDiffOn.smul (cd_opW 2 h)

theorem cd_Kc {n : ℕ} {F : Chart → E} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F UC) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Kc F) UC := by
  rw [Kc_fun_eq]
  exact ((cd_opW 0 h).const_smul (2 : ℝ)).add (cd_etaE h)

/-- Two successive `η`-Leibniz steps. -/
theorem eta_leib2 (a b : Fin 3) {H : Chart → E} (hH : ContDiffOn ℝ 2 H UC) :
    ∀ p ∈ UC, opW a (opW b (fun p => p.2.2 • H p)) p
      = p.2.2 • opW a (opW b H) p + (if a = 2 then opW b H p else 0)
        + (if b = 2 then opW a H p else 0) := by
  intro p hp
  have h1 : ContDiffOn ℝ 1 H UC := cd_mono (by norm_num) hH
  have hb : ContDiffOn ℝ 1 (opW b H) UC := cd_opW b (n := 1) (by simpa using hH)
  have e1 := opW_congr a (eta_leib b h1) p hp
  rw [e1]
  have hq : ContDiffOn ℝ 1 (fun q : Chart => q.2.2 • opW b H q) UC :=
    (contDiff_snd.comp contDiff_snd).contDiffOn.smul hb
  by_cases hb2 : b = 2
  · subst hb2
    simp only [↓reduceIte]
    have := opW_add a hq h1 p hp
    have h3 := eta_leib a hb p hp
    rw [show (fun q : Chart => q.2.2 • opW 2 H q + H q) = (fun q : Chart => q.2.2 • opW 2 H q) + H from rfl,
      this, h3]
  · simp only [hb2, ite_false, add_zero]
    have h3 := eta_leib a hb p hp
    rw [h3]

/-- Words of length `≤ 2` of `𝒦ψ` are words of length `≤ 3` of `ψ` with `η`-weight. -/
theorem Kc_word_bound {ψ : Chart → E} (hψ : ContDiffOn ℝ 3 ψ UC) {p : Chart} (hp : p ∈ UC)
    {w : List (Fin 3)} (hw : w.length ≤ 2) :
    ‖wordW w (Kc ψ) p‖ ≤ 4 * (1 + |p.2.2|) * SW 3 ψ p := by
  have hψ2 : ContDiffOn ℝ 2 (opW 2 ψ) UC := cd_opW 2 (n := 2) (by simpa using hψ)
  have hψ1 : ContDiffOn ℝ 1 (opW 2 ψ) UC := cd_mono (by norm_num) hψ2
  have hS : ContDiffOn ℝ 2 (opW 0 ψ) UC := cd_opW 0 (n := 2) (by simpa using hψ)
  have hx := abs_nonneg p.2.2
  have hT := SW_nonneg 3 ψ p
  have n1 : ∀ (c : ℝ) (v : E), ‖c • v‖ = |c| * ‖v‖ := fun c v => by rw [norm_smul, Real.norm_eq_abs]
  -- split `𝒦ψ`
  have split : ∀ (u : List (Fin 3)), u.length ≤ 2 →
      wordW u (Kc ψ) p = (2 : ℝ) • wordW (u ++ [0]) ψ p
        + wordW u (fun q : Chart => q.2.2 • opW 2 ψ q) p := by
    intro u hu
    have hc1 : ContDiffOn ℝ ((u.length : ℕ) : WithTop ℕ∞) ((2 : ℝ) • opW 0 ψ) UC :=
      (cd_mono hu hS).const_smul (2 : ℝ)
    have hc2 : ContDiffOn ℝ ((u.length : ℕ) : WithTop ℕ∞) (fun q : Chart => q.2.2 • opW 2 ψ q) UC :=
      cd_mono hu (cd_etaE (n := 2) (by simpa using hψ))
    rw [Kc_fun_eq ψ]
    rw [wordW_add u hc1 hc2 p hp, wordW_smul 2 u (cd_mono hu hS) p hp, wordW_append]
    rfl
  have bd0 : ∀ u : List (Fin 3), u.length ≤ 2 → ‖wordW (u ++ [0]) ψ p‖ ≤ SW 3 ψ p :=
    fun u hu => norm_le_SW (by simp; omega) ψ p
  rw [split w hw]
  refine (norm_add_le _ _).trans ?_
  rw [n1]
  have key : ‖wordW w (fun q : Chart => q.2.2 • opW 2 ψ q) p‖ ≤ (|p.2.2| + 2) * SW 3 ψ p := by
    match w, hw with
    | [], _ =>
      simp only [wordW]
      rw [n1]
      have := norm_le_SW (n := 3) (w := [2]) (by simp) ψ p
      simp only [wordW] at this
      nlinarith
    | [a], _ =>
      simp only [wordW]
      have := eta_leib a hψ1 p hp
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [n1]
      have h1 := norm_le_SW (n := 3) (w := [a, 2]) (by simp) ψ p
      have h2 := norm_le_SW (n := 3) (w := [2]) (by simp) ψ p
      simp only [wordW] at h1 h2
      split_ifs
      · nlinarith
      · simp; nlinarith
    | [a, b], _ =>
      simp only [wordW]
      have := eta_leib2 a b hψ2 p hp
      rw [this]
      have h1 := norm_le_SW (n := 3) (w := [a, b, 2]) (by simp) ψ p
      have h2 := norm_le_SW (n := 3) (w := [b, 2]) (by simp) ψ p
      have h3 := norm_le_SW (n := 3) (w := [a, 2]) (by simp) ψ p
      simp only [wordW] at h1 h2 h3
      have t1 : ‖p.2.2 • opW a (opW b (opW 2 ψ)) p‖ ≤ |p.2.2| * SW 3 ψ p := by
        rw [n1]; gcongr
      have t2 : ‖if a = 2 then opW b (opW 2 ψ) p else 0‖ ≤ SW 3 ψ p := by
        split_ifs
        · exact h2
        · simpa using hT
      have t3 : ‖if b = 2 then opW a (opW 2 ψ) p else 0‖ ≤ SW 3 ψ p := by
        split_ifs
        · exact h3
        · simpa using hT
      calc _ ≤ ‖p.2.2 • opW a (opW b (opW 2 ψ)) p‖
            + ‖if a = 2 then opW b (opW 2 ψ) p else 0‖
            + ‖if b = 2 then opW a (opW 2 ψ) p else 0‖ := norm_add₃_le
        _ ≤ _ := by nlinarith
    | _ :: _ :: _ :: _, h => simp at h
  have := bd0 w hw
  have e2 : |(2 : ℝ)| = 2 := by norm_num
  rw [e2]
  nlinarith

end

/-! ### The `Θ` embedding -/

/-- `t ↦ (0, t)` as a meridional vector, as a continuous linear map. -/
def Lth : ℝ →L[ℝ] Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => toMer (0, t)
      map_add' := fun a b => by ext i; fin_cases i <;> simp [toMer]
      map_smul' := fun c a => by ext i; fin_cases i <;> simp [toMer] }

theorem Lth_apply (t : ℝ) : Lth t = toMer (0, t) := rfl

theorem norm_Lth (t : ℝ) : ‖Lth t‖ = |t| := by
  rw [Lth_apply]
  unfold toMer
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]
  rw [Real.sqrt_sq_eq_abs]

section
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

theorem opW_clm (a : Fin 3) (L : E →L[ℝ] E') {f : Chart → E} (hf : ContDiffOn ℝ 1 f UC) :
    ∀ p ∈ UC, opW a (fun q => L (f q)) p = L (opW a f p) := by
  intro p hp
  have h1 := diffAt_of_cd hf hp
  have h := (L.hasFDerivAt.comp p h1.hasFDerivAt).fderiv
  fin_cases a <;> simp [opW, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta,
    (show fderiv ℝ (fun q => L (f q)) p = L.comp (fderiv ℝ f p) from h)]

theorem wordW_clm (L : E →L[ℝ] E') : ∀ (w : List (Fin 3)) {f : Chart → E},
    ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC →
    ∀ p ∈ UC, wordW w (fun q => L (f q)) p = L (wordW w f p)
  | [], f, _ => fun p _ => rfl
  | a :: w, f, hf => by
    intro p hp
    have hf' : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC := cd_mono (by simp) hf
    have ih := wordW_clm L w hf'
    have e1 : wordW (a :: w) (fun q => L (f q)) p = opW a (fun q => L (wordW w f q)) p :=
      opW_congr a ih p hp
    rw [e1]
    have c1 : ContDiffOn ℝ 1 (wordW w f) UC := cd_wordW w 1 (by
      convert hf using 2; simp [add_comm])
    exact opW_clm a L c1 p hp

end

theorem kop_Kc (F : Chart → ℝ) (s : ℝ) (x : ℝ × ℝ) (hF : DifferentiableAt ℝ F (s, x)) :
    Kop (fun s' y => F (s', y)) s x = Kc F (s, x) := by
  have hin : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : Chart))
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => F (s, y))
      ((fderiv ℝ F (s, x)).comp ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x :=
    hF.hasFDerivAt.comp x hin
  have hl : HasDerivAt (fun t : ℝ => ((t, x) : Chart)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h2 : HasDerivAt (fun t : ℝ => F (t, x)) (fderiv ℝ F (s, x) (1, (0 : ℝ × ℝ))) s :=
    hF.hasFDerivAt.comp_hasDerivAt s hl
  have e1 : (fderiv ℝ F (s, x)).comp ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
      (ei 1) = fderiv ℝ F (s, x) (0, (0, 1)) := by
    simp [ei]
  simp only [Kop]
  rw [h1.fderiv, h2.deriv, e1]
  simp only [Kc, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dEta, smul_eq_mul]
  rw [show ((1 : ℝ), (0 : ℝ × ℝ)) = ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) from rfl]
  ring

/-- `Θ` is `L ∘ (ψ - 𝒦ψ)` on `s > 0` (source 4979-4980). -/
theorem thetaM_eq (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (hψ : ContDiffOn ℝ 1 (psiM ν χf A) UC) :
    ∀ p ∈ UC, thetaM ν χf A p = Lth ((psiM ν χf A - Kc (psiM ν χf A)) p) := by
  intro p hp
  have hd : DifferentiableAt ℝ (psiM ν χf A) (p.1, p.2) := diffAt_of_cd hψ hp
  have hk := kop_Kc (psiM ν χf A) p.1 p.2 hd
  simp only [thetaM, Lth_apply, Pi.sub_apply]
  have : Kop (fun s' y => psipA ν χf A s' y) p.1 p.2 = Kc (psiM ν χf A) p := hk
  rw [this]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
