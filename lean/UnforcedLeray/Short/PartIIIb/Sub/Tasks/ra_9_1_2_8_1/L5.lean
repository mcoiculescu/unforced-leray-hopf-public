import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fderiv_mul_apply_dir {c G : Chart → ℝ} {p w : Chart} (hc : DifferentiableAt ℝ c p)
    (hG : DifferentiableAt ℝ G p) :
    fderiv ℝ (fun x => c x * G x) p w = c p * fderiv ℝ G p w + G p * fderiv ℝ c p w := by
  rw [show (fun x => c x * G x) = c * G from rfl, fderiv_mul hc hG]
  simp only [add_apply, smul_apply, smul_eq_mul]

theorem diff_of_C2 {U : Set Chart} (hU : IsOpen U) {G : Chart → ℝ} (hG : ContDiffOn ℝ 2 G U)
    {p : Chart} (hp : p ∈ U) : DifferentiableAt ℝ G p :=
  (hG.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)

theorem dir_diff {U : Set Chart} (hU : IsOpen U) {G : Chart → ℝ} (hG : ContDiffOn ℝ 2 G U)
    (w : Chart) {q : Chart} (hq : q ∈ U) :
    DifferentiableAt ℝ (fun p => fderiv ℝ G p w) q := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fun p => fderiv ℝ G p w) U := h1.clm_apply contDiffOn_const
  exact (h2.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num)

theorem fderiv_dir_eventually {F G : Chart → ℝ} {q : Chart} (h : F =ᶠ[nhds q] G) (w : Chart) :
    (fun p => fderiv ℝ F p w) =ᶠ[nhds q] (fun p => fderiv ℝ G p w) := by
  have h2 : fderiv ℝ F =ᶠ[nhds q] fderiv ℝ G := Filter.EventuallyEq.fderiv h
  filter_upwards [h2] with p hp
  show fderiv ℝ F p w = fderiv ℝ G p w
  rw [hp]

theorem fderiv_fst_apply (p w : Chart) : fderiv ℝ (fun x : Chart => x.1) p w = w.1 := by
  have h : HasFDerivAt (fun x : Chart => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  rw [h.fderiv]
  rfl

theorem fderiv_two_fst_apply (p w : Chart) : fderiv ℝ (fun x : Chart => (2:ℝ) * x.1) p w = 2 * w.1 := by
  have h : HasFDerivAt (fun x : Chart => (2:ℝ) * x.1) ((2:ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst.const_mul (2:ℝ)
  rw [h.fderiv]
  simp

theorem fderiv_snd2_apply (p w : Chart) : fderiv ℝ (fun x : Chart => x.2.2) p w = w.2.2 := by
  have h : HasFDerivAt (fun x : Chart => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    HasFDerivAt.comp p hasFDerivAt_snd hasFDerivAt_snd
  rw [h.fderiv]
  simp

/-- Product rule for a coefficient with vanishing `w`-derivative, applied twice. -/
theorem dir_dir_mul {U : Set Chart} (hU : IsOpen U) {q : Chart} (hq : q ∈ U) (w : Chart)
    {c G : Chart → ℝ} (hc : ∀ p, DifferentiableAt ℝ c p) (hcw : ∀ p, fderiv ℝ c p w = 0)
    (hG : ContDiffOn ℝ 2 G U) :
    fderiv ℝ (fun p => fderiv ℝ (fun x => c x * G x) p w) q w
      = c q * fderiv ℝ (fun p => fderiv ℝ G p w) q w := by
  have h1 : (fun p => fderiv ℝ (fun x => c x * G x) p w)
      =ᶠ[nhds q] (fun p => c p * fderiv ℝ G p w) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    show fderiv ℝ (fun x => c x * G x) p w = c p * fderiv ℝ G p w
    rw [fderiv_mul_apply_dir (hc p) (diff_of_C2 hU hG hp), hcw p]
    ring
  have h3 : fderiv ℝ (fun p => fderiv ℝ (fun x => c x * G x) p w) q
      = fderiv ℝ (fun p => c p * fderiv ℝ G p w) q := h1.fderiv_eq
  rw [h3, fderiv_mul_apply_dir (hc q) (dir_diff hU hG w hq), hcw q]
  simp

/-- Difference rule for two directional derivatives applied twice. -/
theorem dir_dir_sub {U : Set Chart} (hU : IsOpen U) {q : Chart} (hq : q ∈ U) (w : Chart)
    {F G : Chart → ℝ} (hF : ContDiffOn ℝ 2 F U) (hG : ContDiffOn ℝ 2 G U) :
    fderiv ℝ (fun p => fderiv ℝ (fun x => F x - G x) p w) q w
      = fderiv ℝ (fun p => fderiv ℝ F p w) q w - fderiv ℝ (fun p => fderiv ℝ G p w) q w := by
  have h1 : (fun p => fderiv ℝ (fun x => F x - G x) p w)
      =ᶠ[nhds q] (fun p => fderiv ℝ F p w - fderiv ℝ G p w) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    show fderiv ℝ (fun x => F x - G x) p w = fderiv ℝ F p w - fderiv ℝ G p w
    rw [show (fun x => F x - G x) = F - G from rfl, fderiv_sub (diff_of_C2 hU hF hp) (diff_of_C2 hU hG hp)]
    simp
  have h3 : fderiv ℝ (fun p => fderiv ℝ (fun x => F x - G x) p w) q
      = fderiv ℝ (fun p => fderiv ℝ F p w - fderiv ℝ G p w) q := h1.fderiv_eq
  have hdiff : fderiv ℝ (fun p => fderiv ℝ F p w - fderiv ℝ G p w) q
      = fderiv ℝ (fun p => fderiv ℝ F p w) q - fderiv ℝ (fun p => fderiv ℝ G p w) q := by
    rw [show (fun p => fderiv ℝ F p w - fderiv ℝ G p w)
        = (fun p => fderiv ℝ F p w) - (fun p => fderiv ℝ G p w) from rfl,
      fderiv_sub (dir_diff hU hF w hq) (dir_diff hU hG w hq)]
  rw [h3, hdiff]
  simp

/-- **Second `q`-derivative of `(1-𝒦)ψ`** (source 5034-5039, 4979-4980): no mixed partial needed,
since `∂_q` kills the coefficients `2s` and `η`. -/
theorem thetaScalDQQ : ThetaScalDQQP := by
  intro ψ q hq hψ
  have hU : IsOpen (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hqU : q ∈ (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hq, mem_univ _⟩
  have hψ2 : ContDiffOn ℝ 2 ψ (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hψ.of_le (by norm_num)
  have hF1 : ContDiffOn ℝ 2 (fderiv ℝ ψ) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hψ.fderiv_of_isOpen hU (by norm_num)
  have hS : ContDiffOn ℝ 2 (UnforcedLeray.Axi.dS ψ) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hF1.clm_apply (contDiffOn_const (c := ((1:ℝ), ((0:ℝ), (0:ℝ)))))
  have hE : ContDiffOn ℝ 2 (UnforcedLeray.Axi.dEta ψ) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hF1.clm_apply (contDiffOn_const (c := ((0:ℝ), ((0:ℝ), (1:ℝ)))))
  have hT : thetaScal ψ = fun x => (ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)
      - x.2.2 * UnforcedLeray.Axi.dEta ψ x := by
    funext x
    simp only [thetaScal, Kc, smul_eq_mul]
    ring
  have hA : ContDiffOn ℝ 2 (fun x : Chart => (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)
      (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun x : Chart => (2:ℝ) * x.1) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ)))).mul hS
  have hB : ContDiffOn ℝ 2 (fun x : Chart => x.2.2 * UnforcedLeray.Axi.dEta ψ x)
      (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun x : Chart => x.2.2) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ)))).mul hE
  have hC : ContDiffOn ℝ 2 (fun x : Chart => ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)
      (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hψ2.sub hA
  have s1 : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
      (ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x) - x.2.2 * UnforcedLeray.Axi.dEta ψ x)) q
      = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
          ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q
        - UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
          x.2.2 * UnforcedLeray.Axi.dEta ψ x)) q :=
    dir_dir_sub hU hqU (0, (1, 0)) hC hB
  have s2 : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
      ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q
      = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ ψ) q
        - UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
          (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q :=
    dir_dir_sub hU hqU (0, (1, 0)) hψ2 hA
  have s3 : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
      (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q
      = (2 * q.1) * UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dS ψ)) q :=
    dir_dir_mul hU hqU (0, (1, 0)) (c := fun x : Chart => (2:ℝ) * x.1)
      (fun p => by fun_prop) (fun p => by simp [fderiv_two_fst_apply]) hS
  have s4 : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (fun x : Chart =>
      x.2.2 * UnforcedLeray.Axi.dEta ψ x)) q
      = q.2.2 * UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dEta ψ)) q :=
    dir_dir_mul hU hqU (0, (1, 0)) (c := fun x : Chart => x.2.2)
      (fun p => by fun_prop) (fun p => by simp [fderiv_snd2_apply]) hE
  have s5 : wordW [1, 1, 0] ψ q = q.1 * UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dS ψ)) q :=
    dir_dir_mul hU hqU (0, (1, 0)) (c := fun x : Chart => x.1)
      (fun p => by fun_prop) (fun p => by simp [fderiv_fst_apply]) hS
  have s6 : wordW [1, 1] ψ q = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ ψ) q := rfl
  have s7 : wordW [1, 1, 2] ψ q = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dEta ψ)) q := rfl
  rw [hT, s1, s2, s3, s4, s5, s6, s7]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
