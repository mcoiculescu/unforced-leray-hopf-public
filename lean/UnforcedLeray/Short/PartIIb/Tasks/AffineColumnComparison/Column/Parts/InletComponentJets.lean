import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets

/-!
# Part II-b, task `PartII-b:G4/3/8/4` (`InletComponentJets`)

Source of record: `the November 2 reference manuscript`, lines 2360-2369.
`e_0 = (-φ_η) m_0 + φ_q m_1` and `e_1 = (φ - 2sφ_s - ηφ_η) m_1` with `φ = cutStream i`.
The jets of `φ` of order `≤ j + 1` come from `cutStreamJets`; the `s`-weighted term is handled by
splitting at `s = H/4` (the cutoff is identically one on `s < H/4`, so `φ_s = 0` there) and using
`s ≤ H` on the rest.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-- Jets of a directional derivative. -/
theorem icj_partial {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : Coord) (l : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ l (fun m => fderiv ℝ φ m v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (l + 1) φ x‖ := by
  have hf : ContDiffAt ℝ ∞ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := ∞) (by simp)).contDiffAt
  refine (norm_iteratedFDeriv_clm_apply_const hf (by exact_mod_cast le_top)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]

/-- Jets of a scalar times a fixed vector. -/
theorem icj_smulVec {g : Coord → ℝ} (hg : ContDiff ℝ ∞ g) (v : Axi.Merid) (l : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ l (fun m => g m • v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ l g x‖ := by
  have h := (ContinuousLinearMap.toSpanSingleton ℝ v).norm_iteratedFDeriv_comp_left
    (f := g) (x := x) (n := l) hg.contDiffAt (by exact_mod_cast le_top)
  rw [ContinuousLinearMap.norm_toSpanSingleton] at h
  exact h

/-- The iterated derivatives of a continuous linear functional. -/
theorem icj_coordNorm (L : Coord →L[ℝ] ℝ) (i : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ i L x‖ ≤ (if i = 0 then ‖L x‖ else 0) + (if i = 1 then ‖L‖ else 0) := by
  rcases i with _ | _ | k
  · simp [norm_iteratedFDeriv_zero]
  · have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := L) (x := x) (n := 0)
    rw [norm_iteratedFDeriv_zero, L.fderiv] at h
    have h' : ‖iteratedFDeriv ℝ 1 (L : Coord → ℝ) x‖ = ‖L‖ := h.symm
    show ‖iteratedFDeriv ℝ 1 (L : Coord → ℝ) x‖ ≤ _
    rw [h']
    simp
  · have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := L) (x := x) (n := k + 1)
    have hf : fderiv ℝ (L : Coord → ℝ) = fun _ => L := funext fun y => L.fderiv
    rw [hf, iteratedFDeriv_succ_const] at h
    simp only [Pi.zero_apply, norm_zero] at h
    rw [← h]
    simp

/-- Leibniz for a coordinate functional times a smooth function. -/
theorem icj_mulCoord (L : Coord →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {F : Coord → ℝ} (hF : ContDiff ℝ ∞ F)
    (l : ℕ) (x : Coord) (b : ℝ) (hb : ∀ i ≤ l, ‖iteratedFDeriv ℝ i F x‖ ≤ b) :
    ‖iteratedFDeriv ℝ l (fun m => L m * F m) x‖ ≤ 2 ^ l * (‖L x‖ + 1) * b := by
  have h0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  refine (norm_iteratedFDeriv_mul_le L.contDiff hF x (by exact_mod_cast le_top)).trans ?_
  have hsum : ∑ i ∈ Finset.range (l + 1),
      (((if i = 0 then ‖L x‖ else 0) + (if i = 1 then (1 : ℝ) else 0))) ≤ ‖L x‖ + 1 := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    split_ifs <;> linarith [norm_nonneg (L x)]
  calc ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (L : Coord → ℝ) x‖ *
        ‖iteratedFDeriv ℝ (l - i) F x‖
      ≤ ∑ i ∈ Finset.range (l + 1), (2 ^ l : ℝ) *
          (((if i = 0 then ‖L x‖ else 0) + (if i = 1 then (1 : ℝ) else 0)) * b) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hc : (l.choose i : ℝ) ≤ 2 ^ l := by exact_mod_cast Nat.choose_le_two_pow l i
        have hn : ‖iteratedFDeriv ℝ i (L : Coord → ℝ) x‖ ≤
            (if i = 0 then ‖L x‖ else 0) + (if i = 1 then (1 : ℝ) else 0) := by
          refine (icj_coordNorm L i x).trans ?_
          have : (if i = 1 then ‖L‖ else 0) ≤ (if i = 1 then (1 : ℝ) else 0) := by
            split_ifs <;> simp [hL]
          linarith
        have hbb := hb (l - i) (Nat.sub_le _ _)
        calc (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (L : Coord → ℝ) x‖ *
              ‖iteratedFDeriv ℝ (l - i) F x‖
            ≤ (2 ^ l : ℝ) * ((if i = 0 then ‖L x‖ else 0) + (if i = 1 then (1 : ℝ) else 0)) * b := by
              gcongr
          _ = _ := by ring
    _ = (2 ^ l : ℝ) * ((∑ i ∈ Finset.range (l + 1),
          (((if i = 0 then ‖L x‖ else 0) + (if i = 1 then (1 : ℝ) else 0)))) * b) := by
        rw [Finset.sum_mul, Finset.mul_sum]
    _ ≤ (2 ^ l : ℝ) * ((‖L x‖ + 1) * b) := by gcongr
    _ = _ := by ring

/-- `∂_s` of the cut stream vanishes on `s < H/4`. -/
theorem icj_dS_zero (p : Params) (i : Fin 2) (hH : 0 < p.H) (hφ : ContDiff ℝ ∞ (p.frozenStream i))
    (x : Coord) (hx : x.1 < p.H / 4) : Axi.dS (p.cutStream i) x = 0 := by
  have hopen : IsOpen {m : Coord | m.1 < p.H / 4} := isOpen_lt continuous_fst continuous_const
  have hev : p.cutStream i =ᶠ[𝓝 x] (fun m : Coord => p.frozenStream i m.2) := by
    filter_upwards [hopen.mem_nhds (show x ∈ {m : Coord | m.1 < p.H / 4} from hx)] with m hm
    have hm' : m.1 ≤ p.H / 4 := le_of_lt hm
    simp only [Params.cutStream, ageCutoff_eq_one hH hm', one_mul]
  unfold Axi.dS
  rw [hev.fderiv_eq]
  have h1 : HasFDerivAt (p.frozenStream i) (fderiv ℝ (p.frozenStream i) x.2) x.2 :=
    ((hφ.differentiable (by simp)) x.2).hasFDerivAt
  have hd : HasFDerivAt (fun m : Coord => p.frozenStream i m.2)
      ((fderiv ℝ (p.frozenStream i) x.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    HasFDerivAt.comp x h1 (hasFDerivAt_snd)
  rw [hd.fderiv]
  exact map_zero (fderiv ℝ (p.frozenStream i) x.2)

/-- `∂_s` of the cut stream vanishes (as a function) on the open set `s < H/4`, hence so do its
iterated derivatives. -/
theorem icj_dS_iter_zero (p : Params) (i : Fin 2) (hH : 0 < p.H)
    (hφ : ContDiff ℝ ∞ (p.frozenStream i)) (x : Coord) (hx : x.1 < p.H / 4) (l : ℕ) :
    iteratedFDeriv ℝ l (fun m : Coord => m.1 * Axi.dS (p.cutStream i) m) x = 0 := by
  have hopen : IsOpen {m : Coord | m.1 < p.H / 4} := isOpen_lt continuous_fst continuous_const
  have hev : (fun m : Coord => m.1 * Axi.dS (p.cutStream i) m) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show x ∈ {m : Coord | m.1 < p.H / 4} from hx)] with m hm
    simp [icj_dS_zero p i hH hφ m hm]
  have := (hev.iteratedFDeriv ℝ l).eq_of_nhds
  rw [this]
  rcases l with _ | l
  · ext; simp
  · rw [iteratedFDeriv_succ_const]; rfl

/-- **Pointwise jets of the inlet components** at a point `x` with `x.1 ≤ H`, given a common bound `b`
on the jets of `φ = cutStream i` of order `≤ j+1` at `x`. -/
theorem icj_pointwise (p : Params) (i : Fin 2) (hH : 0 < p.H)
    (hφ : ContDiff ℝ ∞ (p.cutStream i)) (hfr : ContDiff ℝ ∞ (p.frozenStream i))
    (j : ℕ) (x : Coord) (hx : x.1 ≤ p.H) (b : ℝ)
    (hb : ∀ l ≤ j + 1, ‖iteratedFDeriv ℝ l (p.cutStream i) x‖ ≤ b) (l : ℕ) (hl : l ≤ j) :
    ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ + ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤
      6 * 2 ^ j * (p.H + 1) * (1 + |x.2.2|) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  have hHn : 0 ≤ p.H := hH.le
  have hFD : ∀ v : Coord, ContDiff ℝ ∞ (fun m => fderiv ℝ (p.cutStream i) m v) := fun v =>
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hdir : ∀ v : Coord, ‖v‖ ≤ 1 → ∀ l' ≤ j,
      ‖iteratedFDeriv ℝ l' (fun m => fderiv ℝ (p.cutStream i) m v) x‖ ≤ b := by
    intro v hv l' hl'
    refine (icj_partial hφ v l' x).trans ?_
    calc ‖v‖ * ‖iteratedFDeriv ℝ (l' + 1) (p.cutStream i) x‖ ≤ 1 * b := by
          apply mul_le_mul hv (hb _ (by omega)) (norm_nonneg _) zero_le_one
      _ = b := one_mul b
  have nS : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have nQ : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have nE : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hS : ∀ l' ≤ j, ‖iteratedFDeriv ℝ l' (Axi.dS (p.cutStream i)) x‖ ≤ b := hdir _ nS
  have hQ : ∀ l' ≤ j, ‖iteratedFDeriv ℝ l' (Axi.dQ (p.cutStream i)) x‖ ≤ b := hdir _ nQ
  have hE : ∀ l' ≤ j, ‖iteratedFDeriv ℝ l' (Axi.dEta (p.cutStream i)) x‖ ≤ b := hdir _ nE
  have hFDS : ContDiff ℝ ∞ (Axi.dS (p.cutStream i)) := hFD _
  have hFDQ : ContDiff ℝ ∞ (Axi.dQ (p.cutStream i)) := hFD _
  have hFDE : ContDiff ℝ ∞ (Axi.dEta (p.cutStream i)) := hFD _
  have hm1 : ‖(Axi.m1 : Axi.Merid)‖ = 1 := by simp [Axi.m1]
  have hm0' : ‖-(Axi.m0 : Axi.Merid)‖ = 1 := by simp [Axi.m0]
  have hle : (l : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  -- e0
  have h0 : ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ ≤ 2 * b := by
    have e : inletE0 p i = (fun m => (Axi.dEta (p.cutStream i) m) • (-Axi.m0)) +
        (fun m => (Axi.dQ (p.cutStream i) m) • Axi.m1) := by
      funext m
      simp only [inletE0, Pi.add_apply, smul_neg, neg_smul]
    rw [e, iteratedFDeriv_add_apply]
    · refine (norm_add_le _ _).trans ?_
      have a1 := icj_smulVec hFDE (-Axi.m0) l x
      have a2 := icj_smulVec hFDQ Axi.m1 l x
      rw [hm0'] at a1
      rw [hm1] at a2
      linarith [hQ l hl, hE l hl]
    · exact ((hFDE.smul contDiff_const).of_le hle).contDiffAt
    · exact ((hFDQ.smul contDiff_const).of_le hle).contDiffAt
  -- e1
  have hT1 : ‖iteratedFDeriv ℝ l (fun m : Coord => m.1 * Axi.dS (p.cutStream i) m) x‖ ≤
      2 ^ l * (p.H + 1) * b := by
    by_cases hx4 : x.1 < p.H / 4
    · rw [icj_dS_iter_zero p i hH hfr x hx4 l, norm_zero]; positivity
    · have hpos : 0 < x.1 := by linarith [not_lt.1 hx4]
      have h := icj_mulCoord (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)) (F := Axi.dS (p.cutStream i)) hFDS l x b
        (fun i' hi' => hS i' (hi'.trans hl))
      have hn : ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x‖ ≤ p.H := by
        show ‖x.1‖ ≤ p.H
        rw [Real.norm_eq_abs, abs_of_pos hpos]; exact hx
      refine h.trans ?_
      have : (2 : ℝ) ^ l * (‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x‖ + 1) * b ≤
          2 ^ l * (p.H + 1) * b := by gcongr
      exact this
  have hT2 : ‖iteratedFDeriv ℝ l (fun m : Coord => m.2.2 * Axi.dEta (p.cutStream i) m) x‖ ≤
      2 ^ l * (|x.2.2| + 1) * b := by
    have hL : ‖(ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))‖ ≤ 1 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
      have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
      calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h := icj_mulCoord ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) hL (F := Axi.dEta (p.cutStream i)) hFDE l x b
      (fun i' hi' => hE i' (hi'.trans hl))
    have hn : ‖((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x‖ = |x.2.2| := by
      show ‖x.2.2‖ = _
      exact Real.norm_eq_abs _
    rw [hn] at h
    exact h
  have hC1 : ContDiff ℝ ∞ (fun m : Coord => m.1 * Axi.dS (p.cutStream i) m) :=
    contDiff_fst.mul hFDS
  have hC2 : ContDiff ℝ ∞ (fun m : Coord => m.2.2 * Axi.dEta (p.cutStream i) m) :=
    (contDiff_snd.comp contDiff_snd).mul hFDE
  have hC1' : ContDiff ℝ ∞ (fun m : Coord => (2 : ℝ) • (m.1 * Axi.dS (p.cutStream i) m)) :=
    hC1.const_smul (2 : ℝ)
  have hGs : ContDiff ℝ ∞ (fun m : Coord => (p.cutStream i m - (2 : ℝ) • (m.1 * Axi.dS (p.cutStream i) m)) -
      m.2.2 * Axi.dEta (p.cutStream i) m) := (hφ.sub hC1').sub hC2
  have e1 : inletE1 p i = fun m : Coord => ((p.cutStream i m -
      (2 : ℝ) • (m.1 * Axi.dS (p.cutStream i) m)) - m.2.2 * Axi.dEta (p.cutStream i) m) • Axi.m1 := by
    funext m
    simp only [inletE1, smul_eq_mul]
    congr 1
    ring
  have h1 : ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤
      b + 2 * (2 ^ l * (p.H + 1) * b) + 2 ^ l * (|x.2.2| + 1) * b := by
    rw [e1]
    refine (icj_smulVec hGs Axi.m1 l x).trans ?_
    rw [hm1, one_mul]
    have cA : ContDiffAt ℝ (l : ℕ∞ω) (fun m : Coord => p.cutStream i m -
        (2 : ℝ) • (m.1 * Axi.dS (p.cutStream i) m)) x := ((hφ.sub hC1').of_le hle).contDiffAt
    have cB : ContDiffAt ℝ (l : ℕ∞ω) (fun m : Coord => m.2.2 * Axi.dEta (p.cutStream i) m) x :=
      (hC2.of_le hle).contDiffAt
    have cC : ContDiffAt ℝ (l : ℕ∞ω) (p.cutStream i) x := (hφ.of_le hle).contDiffAt
    have cT : ContDiffAt ℝ (l : ℕ∞ω) (fun m : Coord => m.1 * Axi.dS (p.cutStream i) m) x :=
      (hC1.of_le hle).contDiffAt
    have cD : ContDiffAt ℝ (l : ℕ∞ω) (fun m : Coord => (2 : ℝ) •
        (m.1 * Axi.dS (p.cutStream i) m)) x := (hC1'.of_le hle).contDiffAt
    rw [fun_iteratedFDeriv_sub_apply cA cB]
    refine (norm_sub_le _ _).trans ?_
    rw [fun_iteratedFDeriv_sub_apply cC cD, iteratedFDeriv_const_smul_apply' cT]
    have n1 := norm_sub_le (iteratedFDeriv ℝ l (p.cutStream i) x)
      (iteratedFDeriv ℝ l (fun m : Coord => (2 : ℝ) • (m.1 * Axi.dS (p.cutStream i) m)) x)
    rw [iteratedFDeriv_const_smul_apply' cT, norm_smul, Real.norm_ofNat] at n1
    have := hb l (by omega)
    linarith
  have hJ : (2 : ℝ) ^ l ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hl
  have hP : 1 ≤ p.H + 1 := by linarith
  have hQ1 : 1 ≤ 1 + |x.2.2| := by linarith [abs_nonneg x.2.2]
  have hJ1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hX : 1 ≤ (2 : ℝ) ^ j * ((p.H + 1) * (1 + |x.2.2|)) :=
    one_le_mul_of_one_le_of_one_le hJ1 (one_le_mul_of_one_le_of_one_le hP hQ1)
  have hPQ : p.H + 1 ≤ (p.H + 1) * (1 + |x.2.2|) := le_mul_of_one_le_right (by linarith) hQ1
  have hQP : |x.2.2| + 1 ≤ (p.H + 1) * (1 + |x.2.2|) := by
    nlinarith [abs_nonneg x.2.2]
  have s2 : (2 : ℝ) ^ l * (p.H + 1) ≤ 2 ^ j * ((p.H + 1) * (1 + |x.2.2|)) :=
    mul_le_mul hJ hPQ (by positivity) (by positivity)
  have s3 : (2 : ℝ) ^ l * (|x.2.2| + 1) ≤ 2 ^ j * ((p.H + 1) * (1 + |x.2.2|)) :=
    mul_le_mul hJ hQP (by positivity) (by positivity)
  have key : (2 : ℝ) + (1 + 2 * (2 ^ l * (p.H + 1)) + 2 ^ l * (|x.2.2| + 1)) ≤
      6 * (2 ^ j * ((p.H + 1) * (1 + |x.2.2|))) := by linarith
  calc ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ + ‖iteratedFDeriv ℝ l (inletE1 p i) x‖
      ≤ 2 * b + (b + 2 * (2 ^ l * (p.H + 1) * b) + 2 ^ l * (|x.2.2| + 1) * b) := by linarith
    _ = (2 + (1 + 2 * (2 ^ l * (p.H + 1)) + 2 ^ l * (|x.2.2| + 1))) * b := by ring
    _ ≤ (6 * (2 ^ j * ((p.H + 1) * (1 + |x.2.2|)))) * b := mul_le_mul_of_nonneg_right key hb0
    _ = _ := by ring

/-- Smoothness of both inlet components from smoothness of the cut stream. -/
theorem icj_smooth (p : Params) (i : Fin 2) (hφ : ContDiff ℝ ∞ (p.cutStream i)) :
    ContDiff ℝ ∞ (inletE0 p i) ∧ ContDiff ℝ ∞ (inletE1 p i) := by
  have hFD : ∀ v : Coord, ContDiff ℝ ∞ (fun m => fderiv ℝ (p.cutStream i) m v) := fun v =>
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hFDS : ContDiff ℝ ∞ (Axi.dS (p.cutStream i)) := hFD _
  have hFDQ : ContDiff ℝ ∞ (Axi.dQ (p.cutStream i)) := hFD _
  have hFDE : ContDiff ℝ ∞ (Axi.dEta (p.cutStream i)) := hFD _
  refine ⟨?_, ?_⟩
  · exact (hFDE.neg.smul contDiff_const).add (hFDQ.smul contDiff_const)
  · exact (((hφ.sub ((contDiff_const.mul contDiff_fst).mul hFDS)).sub
      ((contDiff_snd.comp contDiff_snd).mul hFDE)).smul contDiff_const)

theorem inletComponentJets : UnforcedLeray.Short.IIb.InletComponentJets := by
  intro Sig lam q hSig hq dm dp hdm j
  obtain ⟨C0, κ, N, hC0, hκ, hcut⟩ := cutStreamJets lam q hq (j + 1)
  refine ⟨6 * 2 ^ j * (1 + Sig) * C0 * (1 + 1 / Sig) ^ (j + 1), κ, 2 * N + 1, 1, 1,
    by positivity, hκ, one_pos, le_rfl, ?_⟩
  intro p d hreg i
  obtain ⟨hbg, hν, hS, hm⟩ := hreg
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν
  have hc1 : 1 ≤ p.c := by
    rw [hbg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hHdef : p.H = Sig / p.ν := by simp [Params.H, hS]
  have hH0 : 0 < p.H := by rw [hHdef]; positivity
  obtain ⟨hφ, hjet⟩ := hcut p hm hc1 hH0 i
  have hfr : ContDiff ℝ ∞ (p.frozenStream i) := by
    obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
    exact cutJets_frozenStream_cd (hper p.c hc1).1 hm i
  obtain ⟨hs0, hs1⟩ := icj_smooth p i hφ
  refine ⟨hs0, hs1, ?_⟩
  intro l hl x hx
  set E := Real.exp (-(κ * |x.2.2| / p.c)) with hE
  have hEnn : 0 ≤ E := (Real.exp_pos _).le
  have hpt := icj_pointwise p i hH0 hφ hfr j x hx
    (C0 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N * E) (fun l' hl' => hjet l' hl' x) l hl
  refine hpt.trans ?_
  have ha : (1 + p.H⁻¹) ^ (j + 1) ≤ (1 + 1 / Sig) ^ (j + 1) := by
    have : p.H⁻¹ ≤ 1 / Sig := by
      rw [hHdef, inv_div]
      gcongr
    have h2 : 1 + p.H⁻¹ ≤ 1 + 1 / Sig := by linarith
    exact pow_le_pow_left₀ (by positivity) h2 _
  have hHle : p.H + 1 ≤ (1 + Sig) * p.ν⁻¹ := by
    rw [hHdef]
    have : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
    have h4 : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by ring
    rw [h4]
    linarith
  have hcN : p.c ^ N = (p.ν ^ (2 * N))⁻¹ := by
    rw [hbg.c_eq, inv_pow, ← pow_mul]
  have hk : (p.ν ^ (2 * N + 1))⁻¹ = p.ν⁻¹ * (p.ν ^ (2 * N))⁻¹ := by
    rw [pow_succ, mul_inv, mul_comm]
  have hQ : 0 ≤ 1 + |x.2.2| := by positivity
  calc 6 * 2 ^ j * (p.H + 1) * (1 + |x.2.2|) * (C0 * (1 + p.H⁻¹) ^ (j + 1) * p.c ^ N * E)
      ≤ 6 * 2 ^ j * ((1 + Sig) * p.ν⁻¹) * (1 + |x.2.2|) *
          (C0 * (1 + 1 / Sig) ^ (j + 1) * (p.ν ^ (2 * N))⁻¹ * E) := by
        rw [hcN]
        gcongr
    _ = 6 * 2 ^ j * (1 + Sig) * C0 * (1 + 1 / Sig) ^ (j + 1) * (p.ν ^ (2 * N + 1))⁻¹ *
          (1 + |x.2.2|) ^ 1 * E := by
        rw [hk, pow_one]
        ring

end UnforcedLeray.Short.IIb

end
