import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.SepPsiOscFar.PointwisePhi

/-!
# Order-`n` phase-primitive oscillation bound on outward rays (`SepPsiOscFar/IterOscBound.lean`)

Proves `iterFDeriv_srcX0_osc_hpt_le`: for every derivative order `n : ℕ`, on the region
`ε⁻¹ * √ν ≤ ρ`, the `n`-th spatial derivative of the oscillatory difference
`ΔZ τ = srcX0 ν μ (thinSource ε F) τ - srcX0 ν μ (thinSource ε (meanLift (phaseMean c F))) τ`
at `hpt ρ z_y = !₂[ρ, 0, z_y]` satisfies the uniform-in-`τ` bound
`‖iteratedFDeriv ℝ n (ΔZ τ) (hpt ρ z_y)‖ ≤ C * (1 + ν⁻¹ + c) ^ k * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (thinMoment c F).toReal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open UnforcedLeray UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
open YBComm PhasePrim GeomXAsm GeomXAsm.RayFTCAux GeomXAsm.RayPrimAux

namespace SepPsiOscFarAux

/-! ## 1. Joint `C^∞` regularity of `D1` and recursive directional derivatives `HkN` -/

private lemma L2_psi_contDiff_top (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (L2hkPsi t 0) := by
  have hIter : ∀ m : ℕ, iteratedDeriv m (L2hkPsi t 0) = L2hkPsi t m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      exact (L2_psi_hasDeriv t ht m r).deriv
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [hIter m]
  intro r
  exact (L2_psi_hasDeriv t ht m r).differentiableAt

private lemma kjTail_contDiffOn_top :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kjTail {p : ℝ × Space | 0 < p.1} := by
  intro p hp
  have hp1 : 0 < p.1 := hp
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Space => q.1 ^ (-1 / 2 : ℝ)) p :=
    ContDiffAt.rpow_const_of_ne contDiffAt_fst hp1.ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Space => ‖q.2‖ ^ 2 / (4 * q.1)) p := by
    refine ContDiffAt.div ?_ ?_ (by positivity)
    · exact (contDiff_norm_sq ℝ).comp contDiff_snd |>.contDiffAt
    · exact (contDiff_const.mul contDiff_fst).contDiffAt
  exact h1.mul ((L2_psi_contDiff_top 1 one_pos).contDiffAt.comp p h2)

private lemma heatLerayK_jointC_top (i j : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fj i j) {p : ℝ × Space | 0 < p.1} := by
  have hU : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_U
  have hT := kjTail_contDiffOn_top
  have hdiff : ∀ p ∈ {p : ℝ × Space | 0 < p.1}, DifferentiableAt ℝ kjTail p := fun p hp =>
    (hT.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  set ej : Space := UnforcedLeray.coordinateVector j
  set ei : Space := UnforcedLeray.coordinateVector i
  have hG1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p => fderiv ℝ kjTail p (0, ej)) {p : ℝ × Space | 0 < p.1} :=
    (hT.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hG1d : ∀ p ∈ {p : ℝ × Space | 0 < p.1},
      DifferentiableAt ℝ (fun p => fderiv ℝ kjTail p (0, ej)) p := fun p hp =>
    (hG1.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hG2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p => fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) p (0, ei))
      {p : ℝ × Space | 0 < p.1} :=
    (hG1.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Space => IIIa.heatG p.1 p.2)
      {p : ℝ × Space | 0 < p.1} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hp1 : 0 < p.1 := hp
    unfold IIIa.heatG
    refine ContDiffAt.mul ?_ ?_
    · exact ContDiffAt.rpow_const_of_ne (by fun_prop) (by positivity)
    · refine Real.contDiff_exp.contDiffAt.comp p ?_
      refine ContDiffAt.div ?_ ?_ (by positivity)
      · exact (((contDiff_norm_sq ℝ).comp contDiff_snd).neg).contDiffAt
      · exact (contDiff_const.mul contDiff_fst).contDiffAt
  have hpart : ∀ t : ℝ, 0 < t → ∀ x : Space, IIIa.part2 (IIIa.heatTail t) i j x =
      fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) (t, x) (0, ei) := by
    intro t ht x
    have hsl : ∀ y : Space, (t, y) ∈ {p : ℝ × Space | 0 < p.1} := fun y => ht
    have hfun : IIIa.heatTail t = fun y => kjTail (t, y) := funext fun y => kj_heatTail_eq t ht y
    unfold IIIa.part2
    rw [hfun]
    have e1 : (fun y => fderiv ℝ (fun y' => kjTail (t, y')) y ej) =
        fun y => fderiv ℝ kjTail (t, y) (0, ej) :=
      funext fun y => kj_slice_fderiv hU hdiff t ej hsl y
    rw [e1]
    exact kj_slice_fderiv hU hG1d t ei hsl x
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Space =>
      (if i = j then IIIa.heatG p.1 p.2 else 0) +
      fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) p (0, ei)) {p : ℝ × Space | 0 < p.1} := by
    refine ContDiffOn.add ?_ hG2
    by_cases h : i = j
    · simp only [h, ↓reduceIte]; exact hG
    · simp only [h, ↓reduceIte]; exact contDiffOn_const
  refine hsum.congr ?_
  intro p hp
  simp only [Fj, IIIa.heatLerayK, hpart p.1 hp p.2]

private lemma D1_cd_top (i j k : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (D1 i j k) {p : ℝ × Space | 0 < p.1} := by
  have h := (heatLerayK_jointC_top i j).fderiv_of_isOpen isOpen_U (m := ∞) (by simp)
  exact h.clm_apply contDiffOn_const

/-- Recursive `n`-th spatial directional derivative of `D1 i j k` on `ℝ × Space`. -/
private def HkN : (n : ℕ) → Fin 3 → Fin 3 → Fin 3 → (Fin n → Space) → ℝ × Space → ℝ
  | 0, i, j, k, _ => D1 i j k
  | n + 1, i, j, k, m => fun p => fderiv ℝ (HkN n i j k (Fin.tail m)) p ((0 : ℝ), m 0)

private lemma HkN_cd (n : ℕ) (i j k : Fin 3) (m : Fin n → Space) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (HkN n i j k m) {p : ℝ × Space | 0 < p.1} := by
  induction n with
  | zero => exact D1_cd_top i j k
  | succ n ih =>
    have h := (ih (Fin.tail m)).fderiv_of_isOpen isOpen_U (m := ∞) (by simp)
    exact h.clm_apply contDiffOn_const

private lemma HkN_inr (n : ℕ) (i j k : Fin 3) (m : Fin n → Space) {s : ℝ} (hs : 0 < s)
    (x : Space) :
    HasFDerivAt (fun x' : Space => HkN n i j k m (s, x'))
      ((fderiv ℝ (HkN n i j k m) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
  (((HkN_cd n i j k m).contDiffAt (isOpen_U.mem_nhds
    (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs))).differentiableAt
    (by simp)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)

private lemma HkN_eq (n : ℕ) (i j k : Fin 3) (m : Fin n → Space) {s : ℝ} (hs : 0 < s)
    (x : Space) :
    HkN n i j k m (s, x) =
      iteratedFDeriv ℝ n (fun y =>
        fderiv ℝ (fun z => heatLerayK s i j z) y (UnforcedLeray.coordinateVector k)) x m := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    exact D1_eq i j k hs x
  | succ n ih =>
    set g : Space → ℝ := fun y =>
      fderiv ℝ (fun z => heatLerayK s i j z) y (UnforcedLeray.coordinateVector k)
    have hg : ContDiff ℝ ∞ g := h2_smooth i j k hs
    have hfun : (fun x' : Space => HkN n i j k (Fin.tail m) (s, x')) =
        fun x' : Space => iteratedFDeriv ℝ n g x' (Fin.tail m) :=
      funext fun x' => ih (Fin.tail m) x'
    have hinr : HkN (n + 1) i j k m (s, x) =
        fderiv ℝ (fun x' : Space => HkN n i j k (Fin.tail m) (s, x')) x (m 0) := by
      rw [(HkN_inr n i j k (Fin.tail m) hs x).fderiv]
      rfl
    rw [hinr, hfun]
    have hd_iter : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.contDiffAt.iteratedFDeriv_right (m := ∞) (i := n) (by simp)).differentiableAt (by simp)
    let Ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℝ (Fin.tail m)
    have hcomp : HasFDerivAt (fun x' => iteratedFDeriv ℝ n g x' (Fin.tail m))
        (Ev.comp (fderiv ℝ (iteratedFDeriv ℝ n g) x)) x :=
      Ev.hasFDerivAt.comp x hd_iter.hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.apply_apply, ← iteratedFDeriv_succ_apply_left]

private lemma HkN_dd (n : ℕ) (i j k : Fin 3) (m : Fin n → Space) {p : ℝ × Space} (hp : 0 < p.1) :
    DifferentiableAt ℝ (fderiv ℝ (HkN n i j k m)) p :=
  (((HkN_cd n i j k m).contDiffAt (isOpen_U.mem_nhds
    (show p ∈ {p : ℝ × Space | 0 < p.1} from hp))).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)

private lemma HkN_succ_fderiv (n : ℕ) (i j k : Fin 3) (m : Fin (n + 1) → Space)
    {p : ℝ × Space} (hp : 0 < p.1) (v : ℝ × Space) :
    fderiv ℝ (HkN (n + 1) i j k m) p v =
      fderiv ℝ (fderiv ℝ (HkN n i j k (Fin.tail m))) p v ((0 : ℝ), m 0) := by
  have h := (HkN_dd n i j k (Fin.tail m) hp).hasFDerivAt.clm_apply
    (hasFDerivAt_const ((0 : ℝ), m 0) p)
  have hfd : fderiv ℝ (HkN (n + 1) i j k m) p = _ := h.fderiv
  rw [hfd]
  simp

private lemma dt_D1_smooth (i j k : Fin 3) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
      (UnforcedLeray.coordinateVector k)) s) := by
  have hFi : ContDiffOn ℝ 3 (fun p : ℝ × Space => heatLerayK p.1 i j p.2)
      {p : ℝ × Space | 0 < p.1} := heatLerayK_jointC3 i j
  have hK : ContDiff ℝ ∞ (fun y => heatLerayK s i j y) := heatLerayKSmoothAll s hs i j
  have hFun : (fun y' : Space => fderiv ℝ (fun p : ℝ × Space => heatLerayK p.1 i j p.2) (s, y')
      ((1 : ℝ), (0 : Space))) = fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK s i j x') z
          (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l) :=
    funext fun y' => farKer_fderiv_time i j hs y'
  have hfun : (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
      (UnforcedLeray.coordinateVector k)) s) =
      fun y => fderiv ℝ (fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK s i j x') z
          (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) y
          (UnforcedLeray.coordinateVector k) := by
    funext y
    rw [← hFun]
    exact farKer_swap (fun p : ℝ × Space => heatLerayK p.1 i j p.2) hFi hs y _
  rw [hfun]
  have hS : ContDiff ℝ ∞ (fun y' : Space => ∑ l : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK s i j x') z
        (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) := by
    refine ContDiff.sum fun l _ => ?_
    exact (((hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hS.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private lemma HkN_dt_eq (n : ℕ) (i j k : Fin 3) (m : Fin n → Space) {s : ℝ} (hs : 0 < s)
    (x : Space) :
    fderiv ℝ (HkN n i j k m) (s, x) ((1 : ℝ), (0 : Space)) =
      iteratedFDeriv ℝ n (fun y => deriv (fun s' =>
        fderiv ℝ (fun x' => heatLerayK s' i j x') y (UnforcedLeray.coordinateVector k)) s) x m := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    have hEq : (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') x
        (UnforcedLeray.coordinateVector k)) =ᶠ[𝓝 s] fun s' => D1 i j k (s', x) := by
      filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds hs] with s' hs'
      exact (D1_eq i j k hs' x).symm
    rw [hEq.deriv_eq]
    have h1 : HasDerivAt (fun s' : ℝ => ((s', x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
    exact (((D1_d i j k (p := (s, x)) hs).hasFDerivAt.comp_hasDerivAt s h1).deriv).symm
  | succ n ih =>
    set h_dt : Space → ℝ := fun y => deriv (fun s' =>
      fderiv ℝ (fun x' => heatLerayK s' i j x') y (UnforcedLeray.coordinateVector k)) s
    have hsm : ContDiff ℝ ∞ h_dt := dt_D1_smooth i j k hs
    have hfun : (fun y : Space =>
        fderiv ℝ (HkN n i j k (Fin.tail m)) (s, y) ((1 : ℝ), (0 : Space))) =
        fun y : Space => iteratedFDeriv ℝ n h_dt y (Fin.tail m) :=
      funext fun y => ih (Fin.tail m) y
    have hswap : fderiv ℝ (HkN (n + 1) i j k m) (s, x) ((1 : ℝ), (0 : Space)) =
        fderiv ℝ (fun y : Space =>
          fderiv ℝ (HkN n i j k (Fin.tail m)) (s, y) ((1 : ℝ), (0 : Space))) x (m 0) := by
      rw [HkN_succ_fderiv n i j k m (p := (s, x)) hs]
      have hR := (HkN_dd n i j k (Fin.tail m) (p := (s, x)) hs).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_right s x)
      have hR2 := hR.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) x)
      have hR3 : HasFDerivAt (fun y : Space => fderiv ℝ (HkN n i j k (Fin.tail m)) (s, y)
        ((1 : ℝ), (0 : Space))) _ x := hR2
      rw [hR3.fderiv]
      have hsymm : IsSymmSndFDerivAt ℝ (HkN n i j k (Fin.tail m)) (s, x) :=
        ((HkN_cd n i j k (Fin.tail m)).contDiffAt (isOpen_U.mem_nhds
          (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs))).isSymmSndFDerivAt (by simp)
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        zero_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.inr_apply, map_zero, zero_add]
      exact (hsymm _ _).symm
    rw [hswap, hfun]
    have hd_iter : DifferentiableAt ℝ (iteratedFDeriv ℝ n h_dt) x :=
      (hsm.contDiffAt.iteratedFDeriv_right (m := ∞) (i := n) (by simp)).differentiableAt (by simp)
    let Ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℝ (Fin.tail m)
    have hcomp : HasFDerivAt (fun y => iteratedFDeriv ℝ n h_dt y (Fin.tail m))
        (Ev.comp (fderiv ℝ (iteratedFDeriv ℝ n h_dt) x)) x :=
      Ev.hasFDerivAt.comp x hd_iter.hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.apply_apply, ← iteratedFDeriv_succ_apply_left]

private theorem kerPackN (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (i j k : Fin 3) (s : ℝ), 0 < s →
    ∀ x : Space, x ≠ 0 → ∀ (m : Fin n → Space), (∀ r : Fin n, ‖m r‖ ≤ 1) → ∀ v : Space,
      ‖HkN n i j k m (s, x)‖ ≤ C * ‖x‖ ^ (-4 - (n : ℝ)) ∧
      ‖fderiv ℝ (HkN n i j k m) (s, x) ((1 : ℝ), (0 : Space))‖ ≤
        C * ‖x‖ ^ (-6 - (n : ℝ)) ∧
      ‖fderiv ℝ (HkN n i j k m) (s, x) ((0 : ℝ), v)‖ ≤
        C * ‖v‖ * ‖x‖ ^ (-5 - (n : ℝ)) := by
  obtain ⟨Cn, hCn⟩ := sepKernelBounds n
  obtain ⟨Cn1, hCn1⟩ := sepKernelBounds (n + 1)
  obtain ⟨Cd, _, hCd⟩ := farKer_n n
  refine ⟨|Cn| + |Cn1| + |Cd| + 1, by positivity, ?_⟩
  intro i j k s hs x hx m hm v
  have hprod_le : ∏ r : Fin n, ‖m r‖ ≤ 1 :=
    Finset.prod_le_one (fun r _ => norm_nonneg _) (fun r _ => hm r)
  set g : Space → ℝ := fun y =>
    fderiv ℝ (fun z => heatLerayK s i j z) y (UnforcedLeray.coordinateVector k)
  -- 1. Value bound
  have b1 : ‖HkN n i j k m (s, x)‖ ≤ |Cn| * ‖x‖ ^ (-4 - (n : ℝ)) := by
    rw [HkN_eq n i j k m hs x]
    have h_op := (iteratedFDeriv ℝ n g x).le_opNorm m
    have h_dir := farKer_dir (hk_smooth i j hs) (UnforcedLeray.coordinateVector k) x n
    have h_ker := (hCn x hx i j).1 s hs
    have hp : 0 ≤ ‖x‖ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h_ker' : ‖iteratedFDeriv ℝ (n + 1) (fun y => heatLerayK s i j y) x‖ ≤
        |Cn| * ‖x‖ ^ (-4 - (n : ℝ)) :=
      h_ker.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
    have h_g : ‖iteratedFDeriv ℝ n g x‖ ≤ |Cn| * ‖x‖ ^ (-4 - (n : ℝ)) := by
      refine h_dir.trans ?_
      calc ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k)‖ *
            ‖iteratedFDeriv ℝ (n + 1) (fun y => heatLerayK s i j y) x‖
          ≤ 1 * ‖iteratedFDeriv ℝ (n + 1) (fun y => heatLerayK s i j y) x‖ :=
            mul_le_mul_of_nonneg_right ((apply_le _).trans (ek_norm k).le) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h_ker'
    calc ‖iteratedFDeriv ℝ n g x m‖
        ≤ ‖iteratedFDeriv ℝ n g x‖ * ∏ r : Fin n, ‖m r‖ := h_op
      _ ≤ (|Cn| * ‖x‖ ^ (-4 - (n : ℝ))) * 1 :=
          mul_le_mul h_g hprod_le (Finset.prod_nonneg fun r _ => norm_nonneg _) (by positivity)
      _ = |Cn| * ‖x‖ ^ (-4 - (n : ℝ)) := mul_one _
  -- 2. Time derivative bound
  have b2 : ‖fderiv ℝ (HkN n i j k m) (s, x) ((1 : ℝ), (0 : Space))‖ ≤
      |Cd| * ‖x‖ ^ (-6 - (n : ℝ)) := by
    rw [HkN_dt_eq n i j k m hs x]
    have h_op := (iteratedFDeriv ℝ n (fun y => deriv (fun s' =>
      fderiv ℝ (fun x' => heatLerayK s' i j x') y (UnforcedLeray.coordinateVector k)) s) x).le_opNorm m
    have h_dt := hCd i j k s hs x hx
    have hp : 0 ≤ ‖x‖ ^ (-6 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h_dt' := h_dt.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
    calc _ ≤ _ * ∏ r : Fin n, ‖m r‖ := h_op
      _ ≤ (|Cd| * ‖x‖ ^ (-6 - (n : ℝ))) * 1 :=
          mul_le_mul h_dt' hprod_le (Finset.prod_nonneg fun r _ => norm_nonneg _) (by positivity)
      _ = |Cd| * ‖x‖ ^ (-6 - (n : ℝ)) := mul_one _
  -- 3. Spatial derivative bound
  have b3 : ‖fderiv ℝ (HkN n i j k m) (s, x) ((0 : ℝ), v)‖ ≤
      |Cn1| * ‖v‖ * ‖x‖ ^ (-5 - (n : ℝ)) := by
    set vm : Fin (n + 1) → Space := @Fin.cons n (fun _ => Space) v m
    have hdef : fderiv ℝ (HkN n i j k m) (s, x) ((0 : ℝ), v) =
        HkN (n + 1) i j k vm (s, x) := by
      simp [HkN, vm]
    rw [hdef, HkN_eq (n + 1) i j k vm hs x]
    have h_op := (iteratedFDeriv ℝ (n + 1) g x).le_opNorm vm
    rw [Fin.prod_univ_succ] at h_op
    have hhead : ‖vm 0‖ = ‖v‖ := rfl
    have htail : (∏ r : Fin n, ‖vm r.succ‖) = ∏ r : Fin n, ‖m r‖ :=
      Finset.prod_congr rfl fun r _ => rfl
    rw [hhead, htail] at h_op
    have h_dir := farKer_dir (hk_smooth i j hs) (UnforcedLeray.coordinateVector k) x (n + 1)
    have h_ker := (hCn1 x hx i j).1 s hs
    have hexp : (-4 - ((n + 1 : ℕ) : ℝ)) = -5 - (n : ℝ) := by push_cast; ring
    rw [hexp] at h_ker
    have hp : 0 ≤ ‖x‖ ^ (-5 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h_ker' : ‖iteratedFDeriv ℝ (n + 1 + 1) (fun y => heatLerayK s i j y) x‖ ≤
        |Cn1| * ‖x‖ ^ (-5 - (n : ℝ)) :=
      h_ker.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
    have h_g : ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ |Cn1| * ‖x‖ ^ (-5 - (n : ℝ)) := by
      refine h_dir.trans ?_
      calc ‖ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.coordinateVector k)‖ *
            ‖iteratedFDeriv ℝ (n + 1 + 1) (fun y => heatLerayK s i j y) x‖
          ≤ 1 * ‖iteratedFDeriv ℝ (n + 1 + 1) (fun y => heatLerayK s i j y) x‖ :=
            mul_le_mul_of_nonneg_right ((apply_le _).trans (ek_norm k).le) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h_ker'
    calc ‖iteratedFDeriv ℝ (n + 1) g x vm‖
        ≤ ‖iteratedFDeriv ℝ (n + 1) g x‖ * (‖v‖ * ∏ r : Fin n, ‖m r‖) := h_op
      _ ≤ (|Cn1| * ‖x‖ ^ (-5 - (n : ℝ))) * (‖v‖ * 1) :=
          mul_le_mul h_g (mul_le_mul_of_nonneg_left hprod_le (norm_nonneg v))
            (mul_nonneg (norm_nonneg v) (Finset.prod_nonneg fun r _ => norm_nonneg _))
            (by positivity)
      _ = |Cn1| * ‖v‖ * ‖x‖ ^ (-5 - (n : ℝ)) := by ring
  have p4 : 0 ≤ ‖x‖ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have p5 : 0 ≤ ‖x‖ ^ (-5 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have p6 : 0 ≤ ‖x‖ ^ (-6 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  refine ⟨b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
  · nlinarith [abs_nonneg Cn, abs_nonneg Cn1, abs_nonneg Cd]
  · nlinarith [abs_nonneg Cn, abs_nonneg Cn1, abs_nonneg Cd]
  · nlinarith [mul_nonneg hv p5, abs_nonneg Cn, abs_nonneg Cn1, abs_nonneg Cd]

/-! ## 2. Phase coefficient `omN` and single-point oscillation estimate (`oscPointN`) -/

private def omN (n : ℕ) (a : ℂ) (ν : ℝ) (z y0 : Space) (i j k : Fin 3) (m : Fin n → Space)
    (l : ℝ) : ℂ :=
  (l : ℂ) ^ a * ((HkN n i j k m (pth ν z y0 l) : ℝ) : ℂ)

private lemma omN_cd (n : ℕ) {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3)
    (m : Fin n → Space) :
    ContDiffOn ℝ 1 (omN n a ν z y0 i j k m) (Ioo 0 1) := by
  have hpath : ContDiff ℝ 1 (pth ν z y0) := by
    unfold pth
    exact (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2))).prodMk
      (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have h1 : ContDiffOn ℝ 1 (fun l => HkN n i j k m (pth ν z y0 l)) (Ioo 0 1) :=
    ((HkN_cd n i j k m).of_le (by simp)).comp hpath.contDiffOn (fun l hl => pth_pos' hν z y0 hl)
  have h2 : ContDiffOn ℝ 1 (fun l => ((HkN n i j k m (pth ν z y0 l) : ℝ) : ℂ)) (Ioo 0 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact (cpow_cd a).mul h2

private lemma omN_form (n : ℕ) {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3)
    (m : Fin n → Space) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    omN n a ν z y0 i j k m l + (l : ℂ) * deriv (omN n a ν z y0 i j k m) l =
      ((1 + a) * (l : ℂ) ^ a) * ((HkN n i j k m (pth ν z y0 l) : ℝ) : ℂ) +
      ((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (HkN n i j k m) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.1.ne'
  have hslit : (l : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using hl.1
  have hc : HasDerivAt (fun l : ℝ => (l : ℂ) ^ a) (a * (l : ℂ) ^ (a - 1)) l :=
    ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt).comp_ofReal
  have hh : HasDerivAt (fun l => HkN n i j k m (pth ν z y0 l))
      (fderiv ℝ (HkN n i j k m) (pth ν z y0 l) (-(2 * ν * l), -z)) l := by
    have hd : DifferentiableAt ℝ (HkN n i j k m) (pth ν z y0 l) :=
      ((HkN_cd n i j k m).contDiffAt (isOpen_U.mem_nhds
        (show pth ν z y0 l ∈ {p : ℝ × Space | 0 < p.1} from pth_pos' hν z y0 hl))).differentiableAt
        (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt l (pth_hasDeriv ν z y0 l)
  have hm := hc.mul hh.ofReal_comp
  have hderiv : deriv (omN n a ν z y0 i j k m) l = _ := hm.deriv
  rw [hderiv]
  have e : (l : ℂ) ^ (a - 1) = (l : ℂ) ^ a / l := by
    rw [Complex.cpow_sub _ _ hl0, Complex.cpow_one]
  rw [e]
  unfold omN
  field_simp
  ring

private lemma omN_bounds (n : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hpk : ∀ (i j k : Fin 3) (s : ℝ), 0 < s → ∀ x : Space, x ≠ 0 →
      ∀ (m : Fin n → Space), (∀ r : Fin n, ‖m r‖ ≤ 1) → ∀ v : Space,
        ‖HkN n i j k m (s, x)‖ ≤ C * ‖x‖ ^ (-4 - (n : ℝ)) ∧
        ‖fderiv ℝ (HkN n i j k m) (s, x) ((1 : ℝ), (0 : Space))‖ ≤
          C * ‖x‖ ^ (-6 - (n : ℝ)) ∧
        ‖fderiv ℝ (HkN n i j k m) (s, x) ((0 : ℝ), v)‖ ≤
          C * ‖v‖ * ‖x‖ ^ (-5 - (n : ℝ)))
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (a : ℂ) (z y0 : Space) (i j k : Fin 3)
    (m : Fin n → Space) (hm : ∀ r : Fin n, ‖m r‖ ≤ 1)
    {g Z : ℝ} (hg : 0 < g) (hZ : ‖z‖ ≤ Z)
    (hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    ‖omN n a ν z y0 i j k m l‖ ≤ l ^ a.re * (C * g ^ (-4 - (n : ℝ))) ∧
    ‖omN n a ν z y0 i j k m l + (l : ℂ) * deriv (omN n a ν z y0 i j k m) l‖ ≤
      l ^ a.re * (‖1 + a‖ * (C * g ^ (-4 - (n : ℝ))) +
        2 * C * g ^ (-6 - (n : ℝ)) + C * Z * g ^ (-5 - (n : ℝ))) := by
  have hx : y0 - l • z ≠ 0 := by
    intro h0; have := hgap l hl; rw [h0, norm_zero] at this; linarith
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  obtain ⟨b1, b2, b3⟩ := hpk i j k _ hs _ hx m hm (-z)
  have hxg : g ≤ ‖y0 - l • z‖ := hgap l hl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have r4 : ‖y0 - l • z‖ ^ (-4 - (n : ℝ)) ≤ g ^ (-4 - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by linarith)
  have r5 : ‖y0 - l • z‖ ^ (-5 - (n : ℝ)) ≤ g ^ (-5 - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by linarith)
  have r6 : ‖y0 - l • z‖ ^ (-6 - (n : ℝ)) ≤ g ^ (-6 - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by linarith)
  have hh : |HkN n i j k m (pth ν z y0 l)| ≤ C * g ^ (-4 - (n : ℝ)) := by
    rw [← Real.norm_eq_abs]
    exact b1.trans (mul_le_mul_of_nonneg_left r4 hC0)
  have hp : pth ν z y0 l = (ν * (1 - l ^ 2), y0 - l • z) := rfl
  have hdec : (-(2 * ν * l), -z) = (-(2 * ν * l)) • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), -z) := by
    ext <;> simp
  have hh' : |fderiv ℝ (HkN n i j k m) (pth ν z y0 l) (-(2 * ν * l), -z)| ≤
      2 * C * g ^ (-6 - (n : ℝ)) + C * Z * g ^ (-5 - (n : ℝ)) := by
    rw [← Real.norm_eq_abs, hdec, map_add, map_smul, hp]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [smul_eq_mul, norm_mul]
      have e1 : ‖-(2 * ν * l)‖ ≤ 2 := by
        rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by have := hl.1; positivity)]
        nlinarith [hl.1, hl.2]
      calc _ ≤ 2 * (C * ‖y0 - l • z‖ ^ (-6 - (n : ℝ))) :=
            mul_le_mul e1 b2 (norm_nonneg _) (by norm_num)
        _ ≤ 2 * (C * g ^ (-6 - (n : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r6 hC0) (by norm_num)
        _ = _ := by ring
    · refine b3.trans ?_
      rw [norm_neg]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hZ hC0) r5
        (Real.rpow_nonneg (norm_nonneg _) _)
        (by have := (norm_nonneg z).trans hZ; positivity)
  have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
  refine ⟨?_, ?_⟩
  · unfold omN
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hh hlr
  · rw [omN_form n hν a z y0 i j k m hl]
    refine (norm_add_le _ _).trans ?_
    have n1 : ‖((1 + a) * (l : ℂ) ^ a) * ((HkN n i j k m (pth ν z y0 l) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (‖1 + a‖ * (C * g ^ (-4 - (n : ℝ)))) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs]
      calc ‖1 + a‖ * l ^ a.re * |HkN n i j k m (pth ν z y0 l)|
          ≤ ‖1 + a‖ * l ^ a.re * (C * g ^ (-4 - (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
    have n2 : ‖((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (HkN n i j k m) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (2 * C * g ^ (-6 - (n : ℝ)) + C * Z * g ^ (-5 - (n : ℝ))) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl.1]
      calc l * l ^ a.re * |fderiv ℝ (HkN n i j k m) (pth ν z y0 l) (-(2 * ν * l), -z)|
          ≤ 1 * l ^ a.re * (2 * C * g ^ (-6 - (n : ℝ)) + C * Z * g ^ (-5 - (n : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hl.2.le hlr) hh' (abs_nonneg _) (by positivity)
        _ = _ := by ring
    linarith

private lemma g_rpow_one_sub_le (n : ℕ) {g ρ B : ℝ} (hg : 0 < g) (hρ : 0 < ρ)
    (hg_le : g ≤ ρ) (hginv : g⁻¹ ≤ B * ρ⁻¹) (hB1 : 1 ≤ B) :
    g ^ (1 - (n : ℝ)) ≤ B ^ n * ρ ^ (1 - (n : ℝ)) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  cases n with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, Real.rpow_one, pow_zero, one_mul]
    exact hg_le
  | succ m =>
    have hexp : (1 - ((m + 1 : ℕ) : ℝ)) = -(m : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_neg hg.le, Real.rpow_neg hρ.le,
      ← Real.inv_rpow hg.le, ← Real.inv_rpow hρ.le,
      Real.rpow_natCast, Real.rpow_natCast]
    have hpow : (g⁻¹) ^ m ≤ (B * ρ⁻¹) ^ m :=
      pow_le_pow_left₀ (inv_nonneg.2 hg.le) hginv m
    rw [mul_pow] at hpow
    have hBm : B ^ m ≤ B ^ (m + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hB0 m) hB1
    calc (g⁻¹) ^ m ≤ B ^ m * (ρ⁻¹) ^ m := hpow
      _ ≤ B ^ (m + 1) * (ρ⁻¹) ^ m :=
          mul_le_mul_of_nonneg_right hBm (pow_nonneg (inv_nonneg.2 hρ.le) m)

set_option maxHeartbeats 800000 in
private theorem oscPointN (n : ℕ) :
    ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k₀ : ℕ), 0 ≤ C ∧
      ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
        ∀ f : ℝ → ℝ, Measurable f → (∀ q, f (q + c) = f q) → (∫ q in Ioc 0 c, f q) = 0 →
        ∀ (z : Space) (ρ z_y q₀ : ℝ), ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo →
          ε⁻¹ * ρi ≤ ρ → ∀ (i j k : Fin 3) (m : Fin n → Space),
            (∀ r : Fin n, ‖m r‖ ≤ 1) →
            ‖∫ l in Ioo (0 : ℝ) 1, omN n (2 * μ + 2) ν z (hpt ρ z_y) i j k m l *
                ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ₑ ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k₀ *
                ε * (1 + |z 2|) * ρ ^ (-4 - (n : ℝ))) *
                ∫⁻ q in Ioc 0 c, ‖f q‖ₑ := by
  intro K hK hRe
  obtain ⟨C, hCpos, hpk⟩ := kerPackN n
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set Λ : ℝ := 3 + 2 * |R|
  have hΛ1 : 1 ≤ Λ := by linarith [abs_nonneg R]
  refine ⟨(2 * Λ + 8) * C, 9 + n, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ f hfm hper hmean z ρ z_y q₀ hz hρ_in i j k m hm
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ_in
  set r : ℝ := ε * ρ
  have hr_in : ρi ≤ r := by
    calc ρi = ε * (ε⁻¹ * ρi) := by rw [mul_inv_cancel_left₀ hε.ne']
      _ ≤ ε * ρ := mul_le_mul_of_nonneg_left hρ_in hε.le
  have hrpos : 0 < r := lt_of_lt_of_le hρi hr_in
  have hd : 0 < r - ρo := by linarith
  set y0 : Space := hpt ρ z_y
  set g : ℝ := (r - ρo) / ε
  have hg : 0 < g := div_pos hd hε
  set Z : ℝ := ρo / ε + |z 2|
  have hzh : hor z ≤ ρo / ε := by
    rw [le_div_iff₀ hε, mul_comm]; exact hz
  have hZ : ‖z‖ ≤ Z := by linarith [norm_le_hor z]
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖ := by
    intro l hl
    have h1 := hor_sub y0 z l hl.1.le
    have h2 : hor y0 = ρ := by
      change UnforcedLeray.Axi.ϱ (hpt ρ z_y) = ρ
      exact ϱ_hpt_of_pos hρ0 z_y
    have h3 : l * hor z ≤ ρo / ε := by
      calc l * hor z ≤ 1 * (ρo / ε) :=
            mul_le_mul hl.2.le hzh (by unfold hor; positivity) (by norm_num)
        _ = _ := one_mul _
    have h4 : g = ρ - ρo / ε := by
      unfold g r
      have : ε ≠ 0 := hε.ne'
      field_simp
    have := hor_le_norm (y0 - l • z)
    linarith
  set a : ℂ := 2 * μ + 2
  have hare : a.re = 2 * μ.re + 2 := by simp [a]
  have hμre := hRe μ hμ
  have hnorm : ‖1 + a‖ ≤ Λ := by
    calc ‖1 + (2 * μ + 2)‖ = ‖(3 : ℂ) + 2 * μ‖ := by congr 1; ring
      _ ≤ ‖(3 : ℂ)‖ + ‖2 * μ‖ := norm_add_le _ _
      _ ≤ 3 + 2 * |R| := by
        rw [norm_mul]
        have h3 : ‖(3 : ℂ)‖ = 3 := by simp
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h3, h2]
        have := hR μ hμ
        have := le_abs_self R
        linarith
  set En : ℝ := Λ * (C * g ^ (-4 - (n : ℝ))) + 2 * C * g ^ (-6 - (n : ℝ)) +
    C * Z * g ^ (-5 - (n : ℝ))
  have gn4 : 0 < g ^ (-4 - (n : ℝ)) := Real.rpow_pos_of_pos hg _
  have gn5 : 0 ≤ g ^ (-5 - (n : ℝ)) := Real.rpow_nonneg hg.le _
  have gn6 : 0 < g ^ (-6 - (n : ℝ)) := Real.rpow_pos_of_pos hg _
  have hEn : 0 < En := by positivity
  have hb := fun l (hl : l ∈ Ioo (0 : ℝ) 1) =>
    omN_bounds n C hCpos.le hpk hν hν1 a z y0 i j k m hm hg hZ hgap hl
  have hkey := osc_abstract phaseIBP (omN n a ν z y0 i j k m) (a.re + 1) En
    (by rw [hare]; linarith) hEn (omN_cd n hν a z y0 i j k m)
    (fun l hl => by
      have := (hb l hl).1
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm En]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      have : 0 ≤ C * g ^ (-4 - (n : ℝ)) := by positivity
      nlinarith [mul_nonneg this (by linarith : 0 ≤ Λ - 1), mul_pos hCpos gn6,
        mul_nonneg (mul_nonneg hCpos.le hZ0) gn5])
    (fun l hl => by
      have := (hb l hl).2
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm En]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      have : 0 ≤ C * g ^ (-4 - (n : ℝ)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hnorm this])
    ε c hε hc f hfm hper hmean q₀
  refine hkey.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hg45 : g ^ (-4 - (n : ℝ)) = g ^ (1 - (n : ℝ)) * g ^ (-5 : ℝ) := by
    rw [← Real.rpow_add hg]; congr 1; ring
  have hg56 : g ^ (-5 - (n : ℝ)) = g ^ (1 - (n : ℝ)) * g ^ (-6 : ℝ) := by
    rw [← Real.rpow_add hg]; congr 1; ring
  have hg67 : g ^ (-6 - (n : ℝ)) = g ^ (1 - (n : ℝ)) * g ^ (-7 : ℝ) := by
    rw [← Real.rpow_add hg]; congr 1; ring
  set E : ℝ := Λ * (C * g ^ (-5 : ℝ)) + 2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ)
  have hE_pos : 0 ≤ 2 * ε * E := by
    have : 0 ≤ g ^ (-5 : ℝ) := Real.rpow_nonneg hg.le _
    have : 0 ≤ g ^ (-6 : ℝ) := Real.rpow_nonneg hg.le _
    have : 0 ≤ g ^ (-7 : ℝ) := Real.rpow_nonneg hg.le _
    positivity
  have hEn_eq : 2 * ε * En = g ^ (1 - (n : ℝ)) * (2 * ε * E) := by
    unfold En E
    conv_lhs => rw [hg45, hg56, hg67]
    ring
  set B : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hρiρo : 0 < ρi - ρo := by linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
    have : 0 ≤ ν⁻¹ := by positivity
    have : 0 ≤ ρi⁻¹ := by positivity
    change 1 ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    linarith
  have hQB : r / (r - ρo) ≤ B := by
    have h1 : r / (r - ρo) ≤ ρi / (ρi - ρo) := by
      rw [div_le_div_iff₀ hd hρiρo]
      nlinarith [mul_nonneg hρo (sub_nonneg.2 hr_in)]
    have n1 : 0 ≤ ν⁻¹ := by positivity
    have n2 : 0 ≤ ρi⁻¹ := by positivity
    change r / (r - ρo) ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    rw [← div_eq_mul_inv]
    linarith
  have hg_le_ρ : g ≤ ρ := by
    have h4 : g = ρ - ρo / ε := by
      unfold g r
      have : ε ≠ 0 := hε.ne'
      field_simp
    have : 0 ≤ ρo / ε := div_nonneg hρo hε.le
    linarith
  have hginv_le : g⁻¹ ≤ B * ρ⁻¹ := by
    have hg_eq : g⁻¹ = (r / (r - ρo)) * ρ⁻¹ := by
      unfold g r
      have hε_ne : ε ≠ 0 := hε.ne'
      have hρ_ne : ρ ≠ 0 := hρ0.ne'
      have hd0 : ε * ρ - ρo ≠ 0 := hd.ne'
      field_simp
    rw [hg_eq]
    exact mul_le_mul_of_nonneg_right hQB (inv_nonneg.2 hρ0.le)
  have hg_pow := g_rpow_one_sub_le n hg hρ0 hg_le_ρ hginv_le hB1
  have hrp := real_part C Λ ε ρo ρi ν c r (z 2) hCpos hΛ1 hν hc hε hε1 hρo hρ hr_in hg
  have hr_pow : r ^ (-5 : ℝ) = ε ^ (-5 : ℝ) * ρ ^ (-5 : ℝ) :=
    Real.mul_rpow hε.le hρ0.le
  have hε_pow : ε ^ (6 : ℕ) * ε ^ (-5 : ℝ) = ε := by
    rw [← Real.rpow_natCast ε 6, ← Real.rpow_add hε]
    norm_num
  have hρ_pow : ρ ^ (1 - (n : ℝ)) * ρ ^ (-5 : ℝ) = ρ ^ (-4 - (n : ℝ)) := by
    rw [← Real.rpow_add hρ0]
    congr 1; ring
  calc 2 * ε * En = g ^ (1 - (n : ℝ)) * (2 * ε * E) := hEn_eq
    _ ≤ (B ^ n * ρ ^ (1 - (n : ℝ))) *
          ((2 * Λ + 8) * C * B ^ 9 * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ)) :=
        mul_le_mul hg_pow hrp hE_pos (by positivity)
    _ = (2 * Λ + 8) * C * (B ^ 9 * B ^ n) * (ε ^ (6 : ℕ) * ε ^ (-5 : ℝ)) *
          (1 + |z 2|) * (ρ ^ (1 - (n : ℝ)) * ρ ^ (-5 : ℝ)) := by
        rw [hr_pow]
        clear_value B
        ring
    _ = (2 * Λ + 8) * C * B ^ (9 + n) * ε * (1 + |z 2|) * ρ ^ (-4 - (n : ℝ)) := by
        rw [← pow_add, hε_pow, hρ_pow]

/-! ## 3. Order-`n` differentiation of `sepW` under the integral sign (`fderivN_sepW_of`) -/

set_option maxHeartbeats 1200000 in
private theorem fderivN_sepW_of (n : ℕ) {ν : ℝ} (hν : 0 < ν) {μ : ℂ} {rOut rIn P : ℝ}
    (hrO : 0 ≤ rOut) (hrr : rOut < rIn) (_hP : 0 < P)
    {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsSepSource P rOut T) (τ : ℝ) (y : Space)
    (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hfin : sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤) :
    ContDiffAt ℝ ∞ (fun y' => sepW ν μ T y' τ) y ∧
      Integrable (fun p => iteratedFDeriv ℝ n (sepDiffF ν μ T τ p) y) sepDiffRho ∧
      iteratedFDeriv ℝ n (fun y' => sepW ν μ T y' τ) y =
        ∫ p, iteratedFDeriv ℝ n (sepDiffF ν μ T τ p) y ∂sepDiffRho := by
  have h1 := heatLerayKSmoothAll
  have h3 := sepDiffFMeas
  have h4 := sepDiffFDerivBound
  have h5 := sepDiffWEqIntegral
  have h6 := sepDiffMajIntegrable
  have hK := sepKernelBounds
  choose C hC0 hC using h4 hK
  have hD : 0 < rIn - rOut := by linarith
  set D := rIn - rOut
  set U : Set Space := Metric.ball y (D / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by linarith)
  set F := sepDiffF ν μ T τ
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => sepDiffF_contDiff h1 ν μ T τ hν p hp i
  have hsmAt : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ m (fun y' => F p y' i) y' := fun m p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => sepDiffF_eq_zero ν μ T τ p (hT.support _ _ hp)
  have hpi : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ m (F p) y'‖ ≤ 3 * C m *
        (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro m p hp y' hne
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt m p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (fun y'' => F p y'' i) y')‖ ≤ C m *
          (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC m ν μ T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ m (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ m (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C m * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  have hgapU : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut →
      ∀ y' ∈ U, D ≤ ‖y - p.1 • p.2‖ ∧ ‖y - p.1 • p.2‖ ≤ 2 * ‖y' - p.1 • p.2‖ := by
    intro p hp hz y' hy'
    have hg := radial_gap y p.2 p.1 rOut rIn hp hz hy
    have hd : ‖y - y'‖ < D / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'
    have ht := norm_sub_le_norm_sub_add_norm_sub y y' (p.1 • p.2)
    exact ⟨hg, by linarith⟩
  have hdom : ∀ (m : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ m (F p) y'‖ ≤
        (3 * C m * 2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ))) * sepDiffMaj μ T τ y p := by
    intro m p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ m hD hg1 hg2
      refine (hpi m p hp y' hne).trans ?_
      unfold sepDiffMaj
      have hC3 : 0 ≤ 3 * C m := by linarith [hC0 m]
      calc 3 * C m * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (m : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C m * (p.1 ^ (2 * μ.re + 2) * (2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · push Not at hz
      rw [hoff p hz]
      have h0 : iteratedFDeriv ℝ m (0 : Space → Fin 3 → ℂ) y' = 0 := by
        simp
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
      unfold sepDiffMaj
      rw [hTz]
      simp [tensorNorm]
  have hInt : Integrable (sepDiffMaj μ T τ y) sepDiffRho :=
    h6 μ rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : L09.LocDominated sepDiffRho F U := by
    intro m x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C m * 2 ^ (4 + (m : ℝ)) * D ^ (-(m : ℝ))) * sepDiffMaj μ T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom m p hp y' hy'
  have hsmooth : ∀ᵐ p ∂sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (m : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ m (F p) x) sepDiffRho := by
    intro m x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ m (fun y' => F p y' i) x)) sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν μ P rOut T hν hT τ i m x)
    refine hR.congr ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt m p hp x i)]
    rfl
  have hFint : ∀ y' ∈ U, Integrable (fun p => F p y') sepDiffRho := by
    intro y' hy'
    have hm : AEStronglyMeasurable (fun p => F p y') sepDiffRho := by
      have := (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).continuous
        |>.comp_aestronglyMeasurable (hmeas 0 y' hy')
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp
    refine Integrable.mono' (hInt.const_mul (3 * C 0 * 2 ^ (4 + ((0 : ℕ) : ℝ)) *
      D ^ (-((0 : ℕ) : ℝ)))) hm ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hdom 0 p hp y' hy'
  have hEq_nhds : (fun y' => sepW ν μ T y' τ) =ᶠ[𝓝 y]
      fun y' => ∫ p, F p y' ∂sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν μ T τ y' (hFint y' hy')
  have hcd_int : ContDiffAt ℝ ∞ (fun y' => ∫ p, F p y' ∂sepDiffRho) y :=
    (L09.contDiffOn_integral hU hsmooth hmeas hLoc).contDiffAt (hU.mem_nhds hyU)
  have hcd : ContDiffAt ℝ ∞ (fun y' => sepW ν μ T y' τ) y :=
    hcd_int.congr_of_eventuallyEq hEq_nhds
  have hIntN : Integrable (fun p => iteratedFDeriv ℝ n (F p) y) sepDiffRho :=
    hLoc.integrable hmeas n hyU
  have hIterN : iteratedFDeriv ℝ n (fun y' => sepW ν μ T y' τ) y =
      ∫ p, iteratedFDeriv ℝ n (F p) y ∂sepDiffRho := by
    rw [(hEq_nhds.iteratedFDeriv ℝ n).self_of_nhds,
      L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc n hyU]
  exact ⟨hcd, hIntN, hIterN⟩

/-! ## 4. Multilinear norm bound, entrywise expansion of `iteratedFDeriv ℝ n sepDiffF`, and `oscFarPtN` -/

private lemma cmmN_enorm_le {n : ℕ} {L : Space [×n]→L[ℝ] (Fin 3 → ℂ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ (m : Fin n → Space) (i : Fin 3), (∀ r : Fin n, ‖m r‖ ≤ 1) → ‖L m i‖ₑ ≤ M) :
    ‖L‖ₑ ≤ M := by
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hM]
  refine ENNReal.ofReal_le_ofReal (L.opNorm_le_bound ENNReal.toReal_nonneg fun m => ?_)
  by_cases hzero : ∃ r : Fin n, ‖m r‖ = 0
  · obtain ⟨r, hr⟩ := hzero
    have hmr : m r = 0 := norm_eq_zero.1 hr
    have hL0 : L m = 0 := L.map_coord_zero r hmr
    have hprod0 : ∏ r' : Fin n, ‖m r'‖ = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) hr
    simp [hL0, hprod0]
  · push Not at hzero
    set u : Fin n → Space := fun r => ‖m r‖⁻¹ • m r
    have hu : ∀ r : Fin n, ‖u r‖ ≤ 1 := by
      intro r
      have hp : 0 < ‖m r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hzero r))
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp.le), inv_mul_cancel₀ (hzero r)]
    have hLu : ‖L u‖ ≤ M.toReal := by
      refine (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 fun i => ?_
      have hi := h u i hu
      rw [← ofReal_norm] at hi
      exact (ENNReal.ofReal_le_iff_le_toReal hM).1 hi
    have hm_eq : m = fun r => ‖m r‖ • u r := by
      funext r
      simp [u, smul_smul, mul_inv_cancel₀ (hzero r)]
    have hL_eq : L m = (∏ r : Fin n, ‖m r‖) • L u := by
      conv_lhs => rw [hm_eq]
      exact L.map_smul_univ (fun r => ‖m r‖) u
    have hprod_nn : 0 ≤ ∏ r : Fin n, ‖m r‖ :=
      Finset.prod_nonneg fun r _ => norm_nonneg _
    rw [hL_eq, norm_smul, Real.norm_of_nonneg hprod_nn, mul_comm]
    exact mul_le_mul_of_nonneg_right hLu hprod_nn

private lemma iterN_sepDiffF_entryF (n : ℕ) {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (j₀ k₀ : Fin 3)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (z y0 : Space) (m : Fin n → Space) (i : Fin 3) :
    (iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 m) i =
      (-2 : ℂ) * ((l : ℂ) ^ (2 * μ + 2) *
        ((HkN n i j₀ k₀ m (pth ν z y0 l) : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)) := by
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  induction n generalizing y0 with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    have hD1 : D1 i j₀ k₀ (pth ν z y0 l) =
        fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x) (y0 - l • z)
          (UnforcedLeray.coordinateVector k₀) :=
      D1_eq i j₀ k₀ hs (y0 - l • z)
    change sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z) y0 i =
      (-2 : ℂ) * ((l : ℂ) ^ (2 * μ + 2) *
        ((D1 i j₀ k₀ (pth ν z y0 l) : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ))
    rw [hD1]
    unfold sepDiffF
    dsimp only
    have hsum : (∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) (y0 - l • z)
          (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
        ((thinSource ε (entryF j₀ k₀ F) (τ + 2 * Real.log l) z j k : ℝ) : ℂ)) =
        ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x) (y0 - l • z)
          (UnforcedLeray.coordinateVector k₀) : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.sum_eq_single k₀]
        · simp [thinSource, entryF]
        · intro k _ hk; simp [thinSource, entryF, hk]
        · intro hk; exact absurd (Finset.mem_univ k₀) hk
      · intro j _ hj
        exact Finset.sum_eq_zero fun k _ => by simp [thinSource, entryF, hj]
      · intro hj; exact absurd (Finset.mem_univ j₀) hj
    rw [hsum]
    ring
  | succ n ih =>
    set Φ := sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)
    have hsm : ContDiff ℝ ∞ Φ :=
      contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ
        (thinSource ε (entryF j₀ k₀ F)) τ hν (l, z) hl)
    have hd_iter : DifferentiableAt ℝ (iteratedFDeriv ℝ n Φ) y0 :=
      (hsm.contDiffAt.iteratedFDeriv_right (m := ∞) (i := n) (by simp)).differentiableAt (by simp)
    let Λ : (Space [×n]→L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) (Fin 3 → ℂ) (Fin.tail m))
    have hcomp : HasFDerivAt (fun y' => (iteratedFDeriv ℝ n Φ y' (Fin.tail m)) i)
        (Λ.comp (fderiv ℝ (iteratedFDeriv ℝ n Φ) y0)) y0 :=
      Λ.hasFDerivAt.comp y0 hd_iter.hasFDerivAt
    have h_lhs : (iteratedFDeriv ℝ (n + 1) Φ y0 m) i =
        fderiv ℝ (fun y' => (iteratedFDeriv ℝ n Φ y' (Fin.tail m)) i) y0 (m 0) := by
      rw [iteratedFDeriv_succ_apply_left, hcomp.fderiv]
      rfl
    have hfun : (fun y' => (iteratedFDeriv ℝ n Φ y' (Fin.tail m)) i) =
        fun y' => (-2 : ℂ) * ((l : ℂ) ^ (2 * μ + 2) *
          ((HkN n i j₀ k₀ (Fin.tail m) (pth ν z y' l) : ℝ) : ℂ) *
          ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)) :=
      funext fun y' => ih y' (Fin.tail m)
    rw [h_lhs, hfun]
    have hHk_at : HasFDerivAt (fun y' : Space => HkN n i j₀ k₀ (Fin.tail m) (pth ν z y' l))
        ((fderiv ℝ (HkN n i j₀ k₀ (Fin.tail m)) (pth ν z y0 l)).comp
          (ContinuousLinearMap.inr ℝ ℝ Space)) y0 := by
      have h1 := (HkN_inr n i j₀ k₀ (Fin.tail m) hs (y0 - l • z)).comp y0
        ((hasFDerivAt_id y0).sub_const (l • z))
      rwa [ContinuousLinearMap.comp_id] at h1
    have hHk_c : HasFDerivAt
        (fun y' : Space => ((HkN n i j₀ k₀ (Fin.tail m) (pth ν z y' l) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ (HkN n i j₀ k₀ (Fin.tail m)) (pth ν z y0 l)).comp
          (ContinuousLinearMap.inr ℝ ℝ Space))) y0 :=
      Complex.ofRealCLM.hasFDerivAt.comp y0 hHk_at
    have hscal := ((hHk_c.const_mul ((l : ℂ) ^ (2 * μ + 2))).mul_const
      ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)).const_mul (-2 : ℂ)
    have hscal' : HasFDerivAt (fun y' : Space => (-2 : ℂ) * ((l : ℂ) ^ (2 * μ + 2) *
        ((HkN n i j₀ k₀ (Fin.tail m) (pth ν z y' l) : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ))) _ y0 := hscal
    rw [hscal'.fderiv]
    simp [HkN]
    ring

private lemma iterN_sepDiffF_sum_entryF (n : ℕ) {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    {p : ℝ × Space} (hp : p.1 ∈ Ioo (0 : ℝ) 1) (y0 : Space) :
    iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε F) τ p) y0 =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
  have hsm : ∀ j₀ k₀ : Fin 3,
      ContDiff ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) := fun j₀ k₀ =>
    (contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ
      (thinSource ε (entryF j₀ k₀ F)) τ hν p hp)).of_le (by exact_mod_cast le_top)
  have hfun : sepDiffF ν μ (thinSource ε F) τ p =
      fun y' => ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y' := by
    rw [sepDiffF_sum_entryF ν ε μ F τ p]
    ext y' i
    simp [Finset.sum_apply]
  rw [hfun]
  have h1 := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (i := n) (u := Finset.univ)
    (f := fun (j₀ : Fin 3) (y' : Space) => ∑ k₀ : Fin 3,
      sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y')
    (fun j₀ _ => ContDiff.sum fun k₀ _ => hsm j₀ k₀)) y0
  simp only [Finset.sum_apply] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun j₀ _ => ?_
  have h2 := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (i := n) (u := Finset.univ)
    (f := fun (k₀ : Fin 3) (y' : Space) =>
      sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p y')
    (fun k₀ _ => hsm j₀ k₀)) y0
  simpa only [Finset.sum_apply] using h2

set_option maxHeartbeats 800000 in
private theorem oscFarPtN (n : ℕ) :
    ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
        ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
          (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
          (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
          (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
          (∀ x' Y i j, ∫ q in Ioc 0 c, F x' Y q i j = 0) →
          IIIa.thinMoment c F ≠ ⊤ →
          ∀ (ρ z_y : ℝ), ε⁻¹ * ρi ≤ ρ → ∀ τ : ℝ,
            ‖iteratedFDeriv ℝ n (fun y => sepW ν μ (thinSource ε F) y τ) (hpt ρ z_y)‖ₑ ≤
              ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k *
                ε⁻¹ * ρ ^ (-4 - (n : ℝ))) * IIIa.thinMoment c F := by
  intro K hK hRe
  obtain ⟨C₀, m₀, hC₀, hOsc⟩ := oscPointN n K hK hRe
  refine ⟨18 * C₀, m₀ + 1, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ F hmeas hper hsupp hzero hN ρ z_y hρ_in τ
  have hth : ThinHyp c ρo F := ⟨hmeas, hper, hsupp⟩
  set y0 : Space := hpt ρ z_y
  set B : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ_in
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    positivity
  have hcB : c ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ ρi⁻¹ := inv_nonneg.2 hρi.le
    change c ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    linarith
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ UnforcedLeray.Axi.ϱ (hpt ρ z_y)
    rw [ϱ_hpt_of_pos hρ0, div_eq_inv_mul]
    exact hρ_in
  have hP : 0 < 2 * ε * c := by positivity
  have hDomF : sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (srcNorm (thinSource ε F)) τ y0 < ⊤ :=
    sepDom_thin_lt_top hε hc hρ (hRe μ hμ) hth hN τ y0
  obtain ⟨_, hIntF, hIterF⟩ := fderivN_sepW_of n hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0 hDomF
  have hIntE : ∀ j₀ k₀ : Fin 3,
      Integrable
        (fun p => iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0)
        sepDiffRho := by
    intro j₀ k₀
    have hNE : IIIa.thinMoment c (entryF j₀ k₀ F) ≠ ⊤ :=
      ne_top_of_le_ne_top hN (thinMoment_entryF_le c F j₀ k₀)
    have hDomE := sepDom_thin_lt_top hε hc hρ (hRe μ hμ) (thinHyp_entryF hth j₀ k₀) hNE τ y0
    exact (fderivN_sepW_of n hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
      (thin_isSep hε (thinHyp_entryF hth j₀ k₀)) τ y0 hy0 hDomE).2.1
  have hEntryBound : ∀ (j₀ k₀ : Fin 3) (m : Fin n → Space) (i : Fin 3),
      (∀ r : Fin n, ‖m r‖ ≤ 1) →
      ‖(∫ p, iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
          ∂sepDiffRho) m i‖ₑ ≤
        ENNReal.ofReal (2 * C₀ * B ^ (m₀ + 1) * ε⁻¹ * ρ ^ (-4 - (n : ℝ))) *
          IIIa.thinMoment c F := by
    intro j₀ k₀ m i hm
    let Λ : (Space [×n]→L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) (Fin 3 → ℂ) m)
    have hΛInt : Integrable (fun p =>
        iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 m i)
        sepDiffRho :=
      Λ.integrable_comp (hIntE j₀ k₀)
    have hΛEq : (∫ p, iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
        ∂sepDiffRho) m i =
        ∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
          iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 m i := by
      have h1 := (Λ.integral_comp_comm (hIntE j₀ k₀)).symm
      simp only [Λ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousMultilinearMap.apply_apply] at h1
      rw [h1]
      exact integral_prod_symm _ hΛInt
    rw [hΛEq]
    have hSlice : ∀ z : Space,
        ‖∫ l in Ioo (0 : ℝ) 1,
            iteratedFDeriv ℝ n
              (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 m i‖ₑ ≤
          ENNReal.ofReal (2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ))) *
            (ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) := by
      intro z
      have hcongr : (∫ l in Ioo (0 : ℝ) 1,
          iteratedFDeriv ℝ n
            (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 m i) =
          (-2 : ℂ) * ∫ l in Ioo (0 : ℝ) 1, omN n (2 * μ + 2) ν z y0 i j₀ k₀ m l *
            ((F (ε * z 0, ε * z 1) (z 2) (q0 ε τ z + ε⁻¹ * Real.log l) j₀ k₀ : ℝ) : ℂ) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
        rw [iterN_sepDiffF_entryF n hν ε μ F τ j₀ k₀ hl z y0 m i,
          thinSource_q0_apply hε F τ l z j₀ k₀]
        rfl
      rw [hcongr, enorm_mul]
      have h2 : ‖(-2 : ℂ)‖ₑ = ENNReal.ofReal 2 := by
        rw [← ofReal_norm]; norm_num
      rw [h2]
      by_cases hz : ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo
      · have hfm : Measurable (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) :=
          (hmeas j₀ k₀).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
        have hpt := hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ
          (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) hfm
          (fun q => by rw [hper]) (hzero (ε * z 0, ε * z 1) (z 2) j₀ k₀)
          z ρ z_y (q0 ε τ z) hz hρ_in i j₀ k₀ m hm
        have hle_q : (∫⁻ q in Ioc 0 c, ‖F (ε * z 0, ε * z 1) (z 2) q j₀ k₀‖ₑ) ≤
            ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) := by
          refine lintegral_mono fun q => ?_
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (l5_abs_le_tensorNorm _ j₀ k₀)
        calc ENNReal.ofReal 2 * _
            ≤ ENNReal.ofReal 2 *
                (ENNReal.ofReal (C₀ * B ^ m₀ * ε * (1 + |z 2|) * ρ ^ (-4 - (n : ℝ))) *
                  ∫⁻ q in Ioc 0 c,
                    ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
              mul_le_mul_right (hpt.trans (mul_le_mul_right hle_q _)) _
          _ = _ := by
              have hpos1 : 0 ≤ 2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ)) := by
                have : 0 ≤ ρ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg hρ0.le _
                positivity
              have heq : ENNReal.ofReal 2 *
                  ENNReal.ofReal (C₀ * B ^ m₀ * ε * (1 + |z 2|) * ρ ^ (-4 - (n : ℝ))) =
                  ENNReal.ofReal (2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ))) *
                    ENNReal.ofReal (1 + |z 2|) := by
                rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hpos1]
                congr 1; ring
              rw [← mul_assoc, heq, mul_assoc]
      · push Not at hz
        have hF0 : ∀ q, F (ε * z 0, ε * z 1) (z 2) q = 0 := by
          intro q
          apply hsupp
          have : Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2) =
              ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
            rw [show (ε * z 0) ^ 2 + (ε * z 1) ^ 2 = ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
          rw [this]; exact hz
        simp [hF0]
    calc ‖∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
            iteratedFDeriv ℝ n
              (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 m i‖ₑ
        ≤ ∫⁻ z : Space, ‖∫ l in Ioo (0 : ℝ) 1,
            iteratedFDeriv ℝ n
              (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 m i‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z : Space,
            ENNReal.ofReal (2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ))) *
              (ENNReal.ofReal (1 + |z 2|) *
                ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
          lintegral_mono hSlice
      _ = ENNReal.ofReal (2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ))) *
            ∫⁻ z : Space, ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ))) *
            (ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)) :=
          mul_le_mul_right (thin_z_moment_le hε hc hth) _
      _ ≤ ENNReal.ofReal (2 * C₀ * B ^ (m₀ + 1) * ε⁻¹ * ρ ^ (-4 - (n : ℝ))) *
            IIIa.thinMoment c F := by
          have hrp_nn : 0 ≤ ρ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg hρ0.le _
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_pow (inv_nonneg.2 hε.le),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hε_inv : ε * (ε⁻¹) ^ 2 = ε⁻¹ := by
            have : ε ≠ 0 := hε.ne'
            field_simp
          have h1 : 2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ)) * (ε⁻¹) ^ 2 * c =
              2 * C₀ * (B ^ m₀ * c) * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) := by
            calc 2 * C₀ * B ^ m₀ * ε * ρ ^ (-4 - (n : ℝ)) * (ε⁻¹) ^ 2 * c
                = 2 * C₀ * B ^ m₀ * (ε * (ε⁻¹) ^ 2) * ρ ^ (-4 - (n : ℝ)) * c := by ring
              _ = 2 * C₀ * (B ^ m₀ * c) * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) := by rw [hε_inv]; ring
          have hBm : B ^ m₀ * c ≤ B ^ (m₀ + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left hcB (pow_nonneg hB0 m₀)
          rw [h1]
          gcongr
  rw [hIterF]
  have hSumInt : (∫ p, iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε F) τ p) y0 ∂sepDiffRho) =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        ∫ p, iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
          ∂sepDiffRho := by
    have hae : ∀ᵐ p ∂sepDiffRho,
        iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε F) τ p) y0 =
          ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
            iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
      filter_upwards [sepDiffRho_ae_mem] with p hp using
        iterN_sepDiffF_sum_entryF n hν ε μ F τ hp y0
    rw [integral_congr_ae hae,
      integral_finsetSum _ fun j₀ _ => integrable_finsetSum _ fun k₀ _ => hIntE j₀ k₀]
    refine Finset.sum_congr rfl fun j₀ _ => ?_
    exact integral_finsetSum _ fun k₀ _ => hIntE j₀ k₀
  rw [hSumInt]
  have hM_ne_top :
      ENNReal.ofReal (18 * C₀ * B ^ (m₀ + 1) * ε⁻¹ * ρ ^ (-4 - (n : ℝ))) *
        IIIa.thinMoment c F ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  refine cmmN_enorm_le hM_ne_top fun m i hm => ?_
  simp only [sum_apply, Finset.sum_apply]
  calc ‖∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          (∫ p, iteratedFDeriv ℝ n
            (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) m i‖ₑ
      ≤ ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          ‖(∫ p, iteratedFDeriv ℝ n
            (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) m i‖ₑ :=
        (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j₀ _ => enorm_sum_le _ _)
    _ ≤ ∑ _j₀ : Fin 3, ∑ _k₀ : Fin 3,
          ENNReal.ofReal (2 * C₀ * B ^ (m₀ + 1) * ε⁻¹ * ρ ^ (-4 - (n : ℝ))) *
            IIIa.thinMoment c F :=
        Finset.sum_le_sum fun j₀ _ => Finset.sum_le_sum fun k₀ _ => hEntryBound j₀ k₀ m i hm
    _ = ENNReal.ofReal (18 * C₀ * B ^ (m₀ + 1) * ε⁻¹ * ρ ^ (-4 - (n : ℝ))) *
          IIIa.thinMoment c F := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        have h9 : ((3 : ℕ) : ℝ≥0∞) * ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 9 := by norm_num
        rw [h9, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-! ## 5. Splitting `iteratedFDeriv ℝ n sepW` and proving `iterFDeriv_srcX0_osc_hpt_le` -/

private lemma sepDiffF_thin_splitN (ν ε c : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (p : ℝ × Space) :
    sepDiffF ν μ (thinSource ε F) τ p =
      sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p +
        sepDiffF ν μ (thinSource ε (perpPart c F)) τ p := by
  ext y' i
  have hthin : ∀ σ z, thinSource ε F σ z =
      thinSource ε (meanLift (IIIa.phaseMean c F)) σ z + thinSource ε (perpPart c F) σ z := by
    intro σ z
    unfold thinSource meanLift perpPart
    simp
  simp only [sepDiffF, Pi.add_apply, hthin]
  simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

private lemma iterN_sepW_thin_split (n : ℕ) {ν c ε ρo ρi : ℝ} {μ : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi)
    (hμ : -(1 / 4) < μ.re) {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hth : ThinHyp c ρo F) (hth1 : ThinHyp c ρo (meanLift (IIIa.phaseMean c F)))
    (hth2 : ThinHyp c ρo (perpPart c F))
    (hN : IIIa.thinMoment c F ≠ ⊤) (hN1 : IIIa.thinMoment c (meanLift (IIIa.phaseMean c F)) ≠ ⊤)
    (hN2 : IIIa.thinMoment c (perpPart c F) ≠ ⊤)
    {ρ : ℝ} (hρ_in : ε⁻¹ * ρi ≤ ρ) (z_y τ : ℝ) :
    iteratedFDeriv ℝ n (fun y => sepW ν μ (thinSource ε F) y τ) (hpt ρ z_y) -
        iteratedFDeriv ℝ n (fun y => sepW ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) y τ)
          (hpt ρ z_y) =
      iteratedFDeriv ℝ n (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (hpt ρ z_y) := by
  set y0 : Space := hpt ρ z_y
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ_in
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ UnforcedLeray.Axi.ϱ (hpt ρ z_y)
    rw [ϱ_hpt_of_pos hρ0, div_eq_inv_mul]
    exact hρ_in
  have hP : 0 < 2 * ε * c := by positivity
  obtain ⟨_, hInt0, hIter0⟩ := fderivN_sepW_of n hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth hN τ y0)
  obtain ⟨_, hInt1, hIter1⟩ := fderivN_sepW_of n hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth1) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth1 hN1 τ y0)
  obtain ⟨_, hInt2, hIter2⟩ := fderivN_sepW_of n hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth2) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth2 hN2 τ y0)
  rw [hIter0, hIter1, hIter2]
  have hae : ∀ᵐ p ∂sepDiffRho,
      iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε F) τ p) y0 =
        iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y0 +
          iteratedFDeriv ℝ n (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y0 := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    have hc1 : ContDiffAt ℝ n
        (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y0 :=
      ((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).of_le
        (by exact_mod_cast le_top)).contDiffAt
    have hc2 : ContDiffAt ℝ n
        (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y0 :=
      ((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).of_le
        (by exact_mod_cast le_top)).contDiffAt
    rw [sepDiffF_thin_splitN ν ε c μ F τ p]
    exact iteratedFDeriv_add_apply hc1 hc2
  rw [integral_congr_ae hae, integral_add hInt1 hInt2, add_sub_cancel_left]

private theorem dnSrcX0_le (n : ℕ) (ν μ : ℝ)
    (src src' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space)
    (hA : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y)
    (hB : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y)
    (hA' : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ) y)
    (hB' : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ) y) :
    ‖iteratedFDeriv ℝ n (fun y' => srcX0 ν μ src τ y' - srcX0 ν μ src' τ y') y‖ ≤
      2 * (‖iteratedFDeriv ℝ n (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y -
            iteratedFDeriv ℝ n (fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ) y‖ +
          ‖iteratedFDeriv ℝ n (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y -
            iteratedFDeriv ℝ n (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ) y‖) := by
  set fA : Space → Fin 3 → ℂ := fun y' => IIIa.sepW ν (μ : ℂ) src y' τ
  set fB : Space → Fin 3 → ℂ := fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ
  set fA' : Space → Fin 3 → ℂ := fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ
  set fB' : Space → Fin 3 → ℂ := fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ
  have hfun : (fun y' => srcX0 ν μ src τ y' - srcX0 ν μ src' τ y') =
      PhasePrim.reMap ∘ ((fA - fA') - (fB - fB')) := by
    funext y'
    change PhasePrim.reMap (fA y' - fB y') - PhasePrim.reMap (fA' y' - fB' y') =
      PhasePrim.reMap ((fA y' - fA' y') - (fB y' - fB' y'))
    rw [← map_sub]
    congr 1
    abel
  rw [hfun]
  have hcd_all : ContDiffAt ℝ ∞ ((fA - fA') - (fB - fB')) y :=
    (hA.sub hA').sub (hB.sub hB')
  have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left PhasePrim.reMap
    hcd_all (n := n) (by exact_mod_cast le_top)
  have hAn : ContDiffAt ℝ n fA y := hA.of_le (by exact_mod_cast le_top)
  have hBn : ContDiffAt ℝ n fB y := hB.of_le (by exact_mod_cast le_top)
  have hA'n : ContDiffAt ℝ n fA' y := hA'.of_le (by exact_mod_cast le_top)
  have hB'n : ContDiffAt ℝ n fB' y := hB'.of_le (by exact_mod_cast le_top)
  have hAA' : ContDiffAt ℝ n (fA - fA') y := hAn.sub hA'n
  have hBB' : ContDiffAt ℝ n (fB - fB') y := hBn.sub hB'n
  have hiter_sub : iteratedFDeriv ℝ n ((fA - fA') - (fB - fB')) y =
      (iteratedFDeriv ℝ n fA y - iteratedFDeriv ℝ n fA' y) -
        (iteratedFDeriv ℝ n fB y - iteratedFDeriv ℝ n fB' y) := by
    rw [iteratedFDeriv_sub_apply hAA' hBB',
      iteratedFDeriv_sub_apply hAn hA'n, iteratedFDeriv_sub_apply hBn hB'n]
  calc ‖iteratedFDeriv ℝ n (PhasePrim.reMap ∘ ((fA - fA') - (fB - fB'))) y‖
      ≤ ‖PhasePrim.reMap‖ * ‖iteratedFDeriv ℝ n ((fA - fA') - (fB - fB')) y‖ := hcomp
    _ ≤ 2 * (‖iteratedFDeriv ℝ n fA y - iteratedFDeriv ℝ n fA' y‖ +
          ‖iteratedFDeriv ℝ n fB y - iteratedFDeriv ℝ n fB' y‖) := by
        rw [hiter_sub]
        exact mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)

private theorem poly_le_13_N (ν c : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) :
    1 + ν⁻¹ + c + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 13 * (1 + ν⁻¹ + c) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := PhasePrim.gap_le ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  linarith

/-- Uniform-in-`τ` oscillation bound for `iteratedFDeriv ℝ n` of
`srcX0 ν μ (thinSource ε F) τ - srcX0 ν μ (thinSource ε (meanLift (phaseMean c F))) τ`
along outward rays `hpt ρ z_y` (`ρ ≥ ε⁻¹ * √ν`). -/
theorem iterFDeriv_srcX0_osc_hpt_le (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ (ν c ε μ : ℝ), 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        ThinHyp c (Real.sqrt (5 * ν / 6)) F →
        IIIa.thinMoment c F ≠ ⊤ →
        ∀ (ρ z_y τ : ℝ), ε⁻¹ * Real.sqrt ν ≤ ρ →
          ‖iteratedFDeriv ℝ n
            (fun w => srcX0 ν μ (IIIa.thinSource ε F) τ w -
              srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ w)
            (hpt ρ z_y)‖ ≤
            C * (1 + ν⁻¹ + c) ^ k * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) *
              (IIIa.thinMoment c F).toReal := by
  obtain ⟨C₀, k₀, hC₀, hOsc⟩ := oscFarPtN n PhasePrim.Kmu PhasePrim.Kmu_compact PhasePrim.Kmu_re
  refine ⟨8 * C₀ * 13 ^ k₀, k₀, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hth hFfin ρ z_y τ hρ_in
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ_in
  have hμK : ((μ : ℝ) : ℂ) ∈ PhasePrim.Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ PhasePrim.Kmu :=
    ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  have hFm := hth.meas
  have hFp := hth.per
  have hFs := hth.supp
  obtain ⟨hm1, hm2⟩ := IIIa.sepMomentSplit c hc F hFm
  have hN1 : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfin hm1
  have hN2 : IIIa.thinMoment c (IIIa.perpPart c F) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hFfin) hm2
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hFm
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hFs x' Y _ h]
  have hth1 : ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  have hth2 : ThinHyp c ρo (IIIa.perpPart c F) :=
    ⟨fun i j => (hFm i j).sub
       ((hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop)),
     fun x' Y q => by simp [IIIa.perpPart, hFp],
     fun x' Y q h => by simp [IIIa.perpPart, hFs x' Y q h, hGs x' Y h]⟩
  set b := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  set M := 1 + ν⁻¹ + c
  have hb0 : 0 ≤ b := by
    have : 0 < ρi - ρo := sub_pos.2 hρ
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
    positivity
  have hM0 : 0 ≤ M := by positivity
  have hble : b ^ k₀ ≤ 13 ^ k₀ * M ^ k₀ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0 (poly_le_13_N ν c hν hν1 hc) k₀
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hy0 : ρi / ε ≤ Real.sqrt ((hpt ρ z_y) 0 ^ 2 + (hpt ρ z_y) 1 ^ 2) := by
    change ρi / ε ≤ UnforcedLeray.Axi.ϱ (hpt ρ z_y)
    rw [ϱ_hpt_of_pos hρ0, div_eq_inv_mul]
    exact hρ_in
  have hP : 0 < 2 * ε * c := by positivity
  have hA := (fderivN_sepW_of n hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
    (thin_isSep hε hth) τ (hpt ρ z_y) hy0
    (sepDom_thin_lt_top hε hc hρ hreμ hth hFfin τ (hpt ρ z_y))).1
  have hB := (fderivN_sepW_of n hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
    (thin_isSep hε hth) τ (hpt ρ z_y) hy0
    (sepDom_thin_lt_top hε hc hρ hreμ1 hth hFfin τ (hpt ρ z_y))).1
  have hA' := (fderivN_sepW_of n hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
    (thin_isSep hε hth1) τ (hpt ρ z_y) hy0
    (sepDom_thin_lt_top hε hc hρ hreμ hth1 hN1 τ (hpt ρ z_y))).1
  have hB' := (fderivN_sepW_of n hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
    (thin_isSep hε hth1) τ (hpt ρ z_y) hy0
    (sepDom_thin_lt_top hε hc hρ hreμ1 hth1 hN1 τ (hpt ρ z_y))).1
  have hsp0 := iterN_sepW_thin_split n hν hc hε hρo hρ hreμ hth hth1 hth2 hFfin hN1 hN2 hρ_in z_y τ
  have hsp1 := iterN_sepW_thin_split n hν hc hε hρo hρ hreμ1 hth hth1 hth2 hFfin hN1 hN2 hρ_in z_y τ
  have hd := dnSrcX0_le n ν μ (IIIa.thinSource ε F)
    (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ (hpt ρ z_y) hA hB hA' hB'
  rw [hsp0, hsp1] at hd
  have hpt0 := (hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ (μ : ℂ) hμK (IIIa.perpPart c F)
    hth2.meas hth2.per hth2.supp (IIIa.perpPart_meanZero c hc F) hN2 ρ z_y hρ_in τ).trans
    (mul_le_mul_right hm2 _)
  have hpt1 := (hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ ((μ : ℂ) + 1) hμ1K (IIIa.perpPart c F)
    hth2.meas hth2.per hth2.supp (IIIa.perpPart_meanZero c hc F) hN2 ρ z_y hρ_in τ).trans
    (mul_le_mul_right hm2 _)
  have hrp_nn : 0 ≤ ρ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg hρ0.le _
  have hK0_nn : 0 ≤ C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) := by positivity
  have h2_eq : (2 : ℝ≥0∞) * IIIa.thinMoment c F =
      ENNReal.ofReal (2 * (IIIa.thinMoment c F).toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hFfin]
  have h_rhs_eq : ENNReal.ofReal (C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ))) *
      (2 * IIIa.thinMoment c F) =
      ENNReal.ofReal (2 * C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) *
        (IIIa.thinMoment c F).toReal) := by
    rw [h2_eq, ← ENNReal.ofReal_mul hK0_nn]
    congr 1; clear_value b; ring
  rw [← ofReal_norm, h_rhs_eq] at hpt0 hpt1
  have hpt0_real : ‖iteratedFDeriv ℝ n
      (fun y => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε (IIIa.perpPart c F)) y τ)
      (hpt ρ z_y)‖ ≤
      2 * C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (IIIa.thinMoment c F).toReal :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hpt0
  have hpt1_real : ‖iteratedFDeriv ℝ n
      (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε (IIIa.perpPart c F)) y τ)
      (hpt ρ z_y)‖ ≤
      2 * C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (IIIa.thinMoment c F).toReal :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hpt1
  calc ‖iteratedFDeriv ℝ n
        (fun w => srcX0 ν μ (IIIa.thinSource ε F) τ w -
          srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ w)
        (hpt ρ z_y)‖
      ≤ 2 * (2 * C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (IIIa.thinMoment c F).toReal +
          2 * C₀ * b ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (IIIa.thinMoment c F).toReal) :=
        hd.trans (mul_le_mul_of_nonneg_left (add_le_add hpt0_real hpt1_real) (by norm_num))
    _ = 8 * C₀ * b ^ k₀ * (ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (IIIa.thinMoment c F).toReal) := by
        clear_value b; ring
    _ ≤ 8 * C₀ * (13 ^ k₀ * M ^ k₀) *
          (ε⁻¹ * ρ ^ (-4 - (n : ℝ)) * (IIIa.thinMoment c F).toReal) := by gcongr
    _ = 8 * C₀ * 13 ^ k₀ * M ^ k₀ * ε⁻¹ * ρ ^ (-4 - (n : ℝ)) *
          (IIIa.thinMoment c F).toReal := by
        clear_value M; ring

end SepPsiOscFarAux

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

end
