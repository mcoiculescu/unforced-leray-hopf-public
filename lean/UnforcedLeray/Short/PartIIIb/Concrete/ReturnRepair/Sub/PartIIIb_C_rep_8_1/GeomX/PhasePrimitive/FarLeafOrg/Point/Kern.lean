import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Kernel

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray.Short.IIIa

/-- joint kernel -/
def Fj (i j : Fin 3) : ℝ × Space → ℝ := fun p => heatLerayK p.1 i j p.2

/-- `x`-derivative of the joint kernel in direction `e_k` -/
def D1 (i j k : Fin 3) : ℝ × Space → ℝ :=
  fun q => fderiv ℝ (Fj i j) q ((0 : ℝ), UnforcedLeray.coordinateVector k)

/-- `D_w ∂_k K` as a joint function -/
def Hk (i j k : Fin 3) (w : Space) : ℝ × Space → ℝ :=
  fun p => fderiv ℝ (D1 i j k) p ((0 : ℝ), w)

lemma isOpen_U : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst

lemma Fj_cd (i j : Fin 3) : ContDiffOn ℝ 3 (Fj i j) {p : ℝ × Space | 0 < p.1} :=
  heatLerayK_jointC3 i j

lemma D1_cd (i j k : Fin 3) : ContDiffOn ℝ 2 (D1 i j k) {p : ℝ × Space | 0 < p.1} := by
  have h := (Fj_cd i j).fderiv_of_isOpen isOpen_U (m := 2) (by norm_num)
  exact h.clm_apply contDiffOn_const

lemma Hk_cd (i j k : Fin 3) (w : Space) : ContDiffOn ℝ 1 (Hk i j k w) {p : ℝ × Space | 0 < p.1} := by
  have h := (D1_cd i j k).fderiv_of_isOpen isOpen_U (m := 1) (by norm_num)
  exact h.clm_apply contDiffOn_const

lemma D1_eq (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (y : Space) :
    D1 i j k (s, y) = fderiv ℝ (fun x => heatLerayK s i j x) y (UnforcedLeray.coordinateVector k) := by
  have hc : HasFDerivAt (fun x' : Space => ((s, x') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y := hasFDerivAt_prodMk_right s y
  have hd : HasFDerivAt (fun x' : Space => Fj i j (s, x'))
      ((fderiv ℝ (Fj i j) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    ((Fj_cd i j).contDiffAt (isOpen_U.mem_nhds (show (s, y) ∈ {p : ℝ × Space | 0 < p.1} from hs))
      |>.differentiableAt (by norm_num)).hasFDerivAt.comp y hc
  have : fderiv ℝ (fun x => heatLerayK s i j x) y =
      (fderiv ℝ (Fj i j) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := hd.fderiv
  rw [this]
  simp [D1]

lemma Hk_eq (i j k : Fin 3) (w : Space) {s : ℝ} (hs : 0 < s) (x : Space) :
    Hk i j k w (s, x) = fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK s i j x) y'
      (UnforcedLeray.coordinateVector k)) x w := by
  have hfun : (fun y' => fderiv ℝ (fun x => heatLerayK s i j x) y'
      (UnforcedLeray.coordinateVector k)) = fun y' => D1 i j k (s, y') :=
    funext fun y' => (D1_eq i j k hs y').symm
  rw [hfun]
  have hD : DifferentiableAt ℝ (D1 i j k) (s, x) :=
    ((D1_cd i j k).contDiffAt (isOpen_U.mem_nhds (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs))
      |>.differentiableAt (by norm_num))
  have hR : HasFDerivAt (fun y' : Space => D1 i j k (s, y'))
      ((fderiv ℝ (D1 i j k) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
    hD.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  rw [hR.fderiv]
  simp [Hk]


lemma apply_le (w : Space) : ‖ContinuousLinearMap.apply ℝ ℝ w‖ ≤ ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)
  simpa [mul_comm] using f.le_opNorm w

lemma ek_norm (k : Fin 3) : ‖UnforcedLeray.coordinateVector k‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

lemma nrm_one {g : Space → ℝ} (x : Space) :
    ‖fderiv ℝ g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]

lemma hk_smooth (i j : Fin 3) {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (fun x => heatLerayK s i j x) :=
  heatLerayKSmoothAll s hs i j

lemma h2_smooth (i j k : Fin 3) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun y' => fderiv ℝ (fun x => heatLerayK s i j x) y'
      (UnforcedLeray.coordinateVector k)) :=
  ((hk_smooth i j hs).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma pack_B1 (C1 : ℝ) (h1 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (1 + 1) (fun y => heatLerayK t i k y) x‖ ≤ C1 * ‖x‖ ^ (-4 - ((1 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) (w : Space) :
    ‖Hk i j k w (s, x)‖ ≤ |C1| * ‖w‖ * ‖x‖ ^ (-5 : ℝ) := by
  rw [Hk_eq i j k w hs x]
  have a := farKer_dir (h2_smooth i j k hs) w x 0
  have b := farKer_dir (hk_smooth i j hs) (UnforcedLeray.coordinateVector k) x 1
  rw [norm_iteratedFDeriv_zero] at a
  have c := h1 x hx i j s hs
  have e : (-4 - ((1 : ℕ) : ℝ)) = -5 := by norm_num
  rw [e] at c
  have hp : 0 ≤ ‖x‖ ^ (-5 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have c' : ‖iteratedFDeriv ℝ (1 + 1) (fun y => heatLerayK s i j y) x‖ ≤ |C1| * ‖x‖ ^ (-5 : ℝ) :=
    c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
  have b' : ‖iteratedFDeriv ℝ 1 (fun y => fderiv ℝ (fun x => heatLerayK s i j x) y
      (UnforcedLeray.coordinateVector k)) x‖ ≤ |C1| * ‖x‖ ^ (-5 : ℝ) := by
    refine b.trans ?_
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ (1 + 1) (fun y => heatLerayK s i j y) x‖ :=
          mul_le_mul_of_nonneg_right ((apply_le _).trans (ek_norm k).le) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact c'
  refine a.trans ?_
  calc _ ≤ ‖w‖ * (|C1| * ‖x‖ ^ (-5 : ℝ)) :=
        mul_le_mul (apply_le w) b' (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

lemma Hk_inr (i j k : Fin 3) (w : Space) {s : ℝ} (hs : 0 < s) (x : Space) :
    HasFDerivAt (fun x' : Space => Hk i j k w (s, x'))
      ((fderiv ℝ (Hk i j k w) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
  (((Hk_cd i j k w).contDiffAt (isOpen_U.mem_nhds
    (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs))).differentiableAt (by norm_num)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right s x)

lemma pack_B3 (C2 : ℝ) (h2 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (2 + 1) (fun y => heatLerayK t i k y) x‖ ≤ C2 * ‖x‖ ^ (-4 - ((2 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) (w v : Space) :
    ‖fderiv ℝ (Hk i j k w) (s, x) ((0 : ℝ), v)‖ ≤ |C2| * ‖w‖ * ‖v‖ * ‖x‖ ^ (-6 : ℝ) := by
  have hfun : (fun x' : Space => Hk i j k w (s, x')) = fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun x => heatLerayK s i j x) y' (UnforcedLeray.coordinateVector k)) x' w :=
    funext fun x' => Hk_eq i j k w hs x'
  have e1 : fderiv ℝ (Hk i j k w) (s, x) ((0 : ℝ), v) =
      fderiv ℝ (fun x' : Space => Hk i j k w (s, x')) x v := by
    rw [(Hk_inr i j k w hs x).fderiv]; simp
  rw [e1, hfun]
  have a := farKer_dir (h2_smooth i j k hs) w x 1
  have b := farKer_dir (hk_smooth i j hs) (UnforcedLeray.coordinateVector k) x 2
  have c := h2 x hx i j s hs
  have e : (-4 - ((2 : ℕ) : ℝ)) = -6 := by norm_num
  rw [e] at c
  have hp : 0 ≤ ‖x‖ ^ (-6 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have c' : ‖iteratedFDeriv ℝ (2 + 1) (fun y => heatLerayK s i j y) x‖ ≤ |C2| * ‖x‖ ^ (-6 : ℝ) :=
    c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
  have b' : ‖iteratedFDeriv ℝ 2 (fun y => fderiv ℝ (fun x => heatLerayK s i j x) y
      (UnforcedLeray.coordinateVector k)) x‖ ≤ |C2| * ‖x‖ ^ (-6 : ℝ) := by
    refine b.trans ?_
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ (2 + 1) (fun y => heatLerayK s i j y) x‖ :=
          mul_le_mul_of_nonneg_right ((apply_le _).trans (ek_norm k).le) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact c'
  have a' : ‖fderiv ℝ (fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun x => heatLerayK s i j x) y' (UnforcedLeray.coordinateVector k)) x' w) x‖ ≤
      ‖w‖ * (|C2| * ‖x‖ ^ (-6 : ℝ)) := by
    rw [nrm_one]
    exact a.trans (mul_le_mul (apply_le w) b' (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ ‖fderiv ℝ (fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun x => heatLerayK s i j x) y' (UnforcedLeray.coordinateVector k)) x' w) x‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖w‖ * (|C2| * ‖x‖ ^ (-6 : ℝ)) * ‖v‖ := mul_le_mul_of_nonneg_right a' (norm_nonneg _)
    _ = _ := by ring


lemma D1_dd (i j k : Fin 3) {p : ℝ × Space} (hp : 0 < p.1) :
    DifferentiableAt ℝ (fderiv ℝ (D1 i j k)) p :=
  (((D1_cd i j k).contDiffAt (isOpen_U.mem_nhds (show p ∈ {p : ℝ × Space | 0 < p.1} from hp))).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)

lemma D1_d (i j k : Fin 3) {p : ℝ × Space} (hp : 0 < p.1) :
    DifferentiableAt ℝ (D1 i j k) p :=
  ((D1_cd i j k).contDiffAt (isOpen_U.mem_nhds (show p ∈ {p : ℝ × Space | 0 < p.1} from hp))).differentiableAt
    (by norm_num)

lemma Hk_fderiv (i j k : Fin 3) (w : Space) {p : ℝ × Space} (hp : 0 < p.1) (v : ℝ × Space) :
    fderiv ℝ (Hk i j k w) p v = fderiv ℝ (fderiv ℝ (D1 i j k)) p v ((0 : ℝ), w) := by
  have h := (D1_dd i j k hp).hasFDerivAt.clm_apply (hasFDerivAt_const ((0 : ℝ), w) p)
  have : fderiv ℝ (Hk i j k w) p = _ := h.fderiv
  rw [this]
  simp

lemma pack_B2 (Cd : ℝ) (hd : ∀ (i j k : Fin 3) (t : ℝ), 0 < t → ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ 1 (fun y => deriv (fun s => fderiv ℝ (fun x' => heatLerayK s i j x') y
        (UnforcedLeray.coordinateVector k)) t) x‖ ≤ Cd * ‖x‖ ^ (-6 - ((1 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) (w : Space) :
    ‖fderiv ℝ (Hk i j k w) (s, x) ((1 : ℝ), (0 : Space))‖ ≤ |Cd| * ‖w‖ * ‖x‖ ^ (-7 : ℝ) := by
  have hg : (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
        (UnforcedLeray.coordinateVector k)) s) =
      fun y => fderiv ℝ (D1 i j k) (s, y) ((1 : ℝ), (0 : Space)) := by
    funext y
    have hEq : (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
        (UnforcedLeray.coordinateVector k)) =ᶠ[𝓝 s] fun s' => D1 i j k (s', y) := by
      filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds hs] with s' hs'
      exact (D1_eq i j k hs' y).symm
    rw [hEq.deriv_eq]
    have h1 : HasDerivAt (fun s' : ℝ => ((s', y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s y)
    exact ((D1_d i j k (p := (s, y)) hs).hasFDerivAt.comp_hasDerivAt s h1).deriv
  have hgd : fderiv ℝ (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
        (UnforcedLeray.coordinateVector k)) s) x w =
      fderiv ℝ (Hk i j k w) (s, x) ((1 : ℝ), (0 : Space)) := by
    rw [hg, Hk_fderiv i j k w (p := (s, x)) hs]
    have hR := (D1_dd i j k (p := (s, x)) hs).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
    have hR2 := hR.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) x)
    have hR3 : HasFDerivAt (fun y : Space => fderiv ℝ (D1 i j k) (s, y) ((1 : ℝ), (0 : Space))) _ x := hR2
    rw [hR3.fderiv]
    have hsymm : IsSymmSndFDerivAt ℝ (D1 i j k) (s, x) :=
      (((D1_cd i j k).contDiffAt (isOpen_U.mem_nhds
        (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs)))).isSymmSndFDerivAt (by norm_num)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.inr_apply, map_zero, zero_add]
    exact hsymm _ _
  rw [← hgd]
  have hb := hd i j k s hs x hx
  have e : (-6 - ((1 : ℕ) : ℝ)) = -7 := by norm_num
  rw [e] at hb
  rw [← nrm_one] at hb
  have hp : 0 ≤ ‖x‖ ^ (-7 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  calc _ ≤ ‖fderiv ℝ (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
        (UnforcedLeray.coordinateVector k)) s) x‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (Cd * ‖x‖ ^ (-7 : ℝ)) * ‖w‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ (|Cd| * ‖x‖ ^ (-7 : ℝ)) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp) (norm_nonneg _)
    _ = _ := by ring

theorem kerPack : ∃ C : ℝ, 0 < C ∧ ∀ (i j k : Fin 3) (s : ℝ), 0 < s → ∀ x : Space, x ≠ 0 →
    ∀ w v : Space,
      ‖Hk i j k w (s, x)‖ ≤ C * ‖w‖ * ‖x‖ ^ (-5 : ℝ) ∧
      ‖fderiv ℝ (Hk i j k w) (s, x) ((1 : ℝ), (0 : Space))‖ ≤ C * ‖w‖ * ‖x‖ ^ (-7 : ℝ) ∧
      ‖fderiv ℝ (Hk i j k w) (s, x) ((0 : ℝ), v)‖ ≤ C * ‖w‖ * ‖v‖ * ‖x‖ ^ (-6 : ℝ) := by
  obtain ⟨C1, hC1⟩ := sepKernelBounds 1
  obtain ⟨C2, hC2⟩ := sepKernelBounds 2
  obtain ⟨Cd, hCd0, hCd⟩ := farKerDt
  refine ⟨|C1| + |C2| + |Cd| + 1, by positivity, ?_⟩
  intro i j k s hs x hx w v
  have b1 := pack_B1 C1 (fun x hx i k t ht => (hC1 x hx i k).1 t ht) i j k hs x hx w
  have b2 := pack_B2 Cd (fun i j k t ht x hx => hCd i j k t ht x hx 1 le_rfl) i j k hs x hx w
  have b3 := pack_B3 C2 (fun x hx i k t ht => (hC2 x hx i k).1 t ht) i j k hs x hx w v
  have hw := norm_nonneg w
  have hv := norm_nonneg v
  have p5 : 0 ≤ ‖x‖ ^ (-5 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have p6 : 0 ≤ ‖x‖ ^ (-6 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have p7 : 0 ≤ ‖x‖ ^ (-7 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
  · have := abs_nonneg C2; have := abs_nonneg Cd
    nlinarith [mul_nonneg hw p5, abs_nonneg C1]
  · have := abs_nonneg C2; have := abs_nonneg C1
    nlinarith [mul_nonneg hw p7, abs_nonneg Cd]
  · have := abs_nonneg Cd; have := abs_nonneg C1
    nlinarith [mul_nonneg (mul_nonneg hw hv) p6, abs_nonneg C2]

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
