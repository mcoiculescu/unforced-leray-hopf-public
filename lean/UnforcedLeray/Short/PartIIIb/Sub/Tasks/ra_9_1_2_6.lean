import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.DcSplitAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slice_fderiv (H : Chart → E) (s : ℝ) (x v : ℝ × ℝ) (h : DifferentiableAt ℝ H (s, x)) :
    fderiv ℝ (fun y => H (s, y)) x v = fderiv ℝ H (s, x) (0, v) := by
  have hι : HasFDerivAt (fun y : ℝ × ℝ => (s, y))
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have := (h.hasFDerivAt.comp x hι).fderiv
  show fderiv ℝ (H ∘ Prod.mk s) x v = _
  rw [this]
  simp

theorem slice_deriv (H : Chart → E) (s : ℝ) (x : ℝ × ℝ) (h : DifferentiableAt ℝ H (s, x)) :
    deriv (fun s' => H (s', x)) s = fderiv ℝ H (s, x) (1, (0, 0)) := by
  have hι : HasDerivAt (fun s' : ℝ => (s', x)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have := (h.hasFDerivAt.comp_hasDerivAt s hι).deriv
  show deriv (H ∘ fun s' => (s', x)) s = _
  rw [this]

theorem openU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ

theorem cdAt {F : Chart → E} {n : ℕ} (hF : ContDiffOn ℝ n F (Ioi 0 ×ˢ univ)) {p : Chart}
    (hp : 0 < p.1) : ContDiffAt ℝ n F p :=
  hF.contDiffAt (openU.mem_nhds ⟨hp, trivial⟩)

theorem ev_mem {q : Chart} (hq : 0 < q.1) : ∀ᶠ p in 𝓝 q, 0 < p.1 :=
  by
  filter_upwards [openU.mem_nhds (⟨hq, trivial⟩ : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))] with p hp
  exact hp.1

theorem dir_cd (v : Chart) {F : Chart → E} {p : Chart} (hF : ContDiffAt ℝ 2 F p) :
    ContDiffAt ℝ 1 (fun p => fderiv ℝ F p v) p := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) p := hF.fderiv_right (by norm_num)
  exact h1.clm_apply contDiffAt_const

theorem dir_add (v : Chart) {F G : Chart → E} (ε : ℝ) {p : Chart} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) :
    fderiv ℝ (F + ε • G) p v = fderiv ℝ F p v + ε • fderiv ℝ G p v := by
  have := (hF.hasFDerivAt.add (hG.hasFDerivAt.const_smul ε)).fderiv
  have h := congrArg (fun L => L v) this
  simpa using h

theorem dir2_add (v w : Chart) {F G : Chart → E} (ε : ℝ) {q : Chart} (hq : 0 < q.1)
    (hF : ContDiffOn ℝ 2 F (Ioi 0 ×ˢ univ)) (hG : ContDiffOn ℝ 2 G (Ioi 0 ×ˢ univ)) :
    fderiv ℝ (fun p => fderiv ℝ (F + ε • G) p w) q v =
      fderiv ℝ (fun p => fderiv ℝ F p w) q v + ε • fderiv ℝ (fun p => fderiv ℝ G p w) q v := by
  have hev : (fun p => fderiv ℝ (F + ε • G) p w) =ᶠ[𝓝 q]
      fun p => fderiv ℝ F p w + ε • fderiv ℝ G p w := by
    filter_upwards [ev_mem hq] with p hp
    exact dir_add w ε ((cdAt hF hp).differentiableAt (by norm_num))
      ((cdAt hG hp).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  have d1 := (dir_cd w (cdAt hF hq)).differentiableAt one_ne_zero
  have d2 := (dir_cd w (cdAt hG hq)).differentiableAt one_ne_zero
  have := (d1.hasFDerivAt.add (d2.hasFDerivAt.const_smul ε)).fderiv
  have h := congrArg (fun L => L v) this
  exact h.trans (by simp)

theorem dc_add (ν μ ε : ℝ) {F G : Chart → E} (hF : ContDiffOn ℝ 2 F (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ 2 G (Ioi 0 ×ˢ univ)) {q : Chart} (hq : 0 < q.1) :
    Dc ν μ (F + ε • G) q = Dc ν μ F q + ε • Dc ν μ G q := by
  have dF := (cdAt hF hq).differentiableAt (by norm_num)
  have dG := (cdAt hG hq).differentiableAt (by norm_num)
  have h1 : UnforcedLeray.Axi.dS (F + ε • G) q = UnforcedLeray.Axi.dS F q + ε • UnforcedLeray.Axi.dS G q := dir_add _ ε dF dG
  have h2 : UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ (F + ε • G)) q = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ F) q + ε • UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ G) q :=
    dir2_add (0, (1, 0)) (0, (1, 0)) ε hq hF hG
  have h3 : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (F + ε • G)) q = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta F) q + ε • UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta G) q :=
    dir2_add (0, (0, 1)) (0, (0, 1)) ε hq hF hG
  simp only [Dc, lapQE, h1, h2, h3, Pi.add_apply, Pi.smul_apply, smul_add, smul_sub]
  rw [smul_comm ν ε, smul_comm ν ε, smul_comm (μ / q.1) ε]
  abel


/-- `toMer` as a continuous linear map. -/
def Lm : ℝ × ℝ →L[ℝ] Merid :=
  LinearMap.toContinuousLinearMap
    { toFun := toMer, map_add' := toMer_add, map_smul' := fun r a => toMer_smul r a }

theorem Lm_apply (v : ℝ × ℝ) : Lm v = toMer v := rfl

/-- The inverse of `toMer`. -/
def fromMer : Merid →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))

theorem fromMer_toMer (v : ℝ × ℝ) : fromMer (toMer v) = v := by
  simp [fromMer, toMer]

theorem dir_toMer (v : Chart) {H : Chart → ℝ × ℝ} {p : Chart} (hH : DifferentiableAt ℝ H p) :
    fderiv ℝ (fun p => toMer (H p)) p v = toMer (fderiv ℝ H p v) := by
  have := (Lm.hasFDerivAt.comp p hH.hasFDerivAt).fderiv
  have h := congrArg (fun L => L v) this
  exact h

theorem dir2_toMer (e : ℝ × ℝ) {H : Chart → ℝ × ℝ} {q : Chart} (hq : 0 < q.1)
    (hH : ∀ p : Chart, 0 < p.1 → ContDiffAt ℝ 2 H p) :
    fderiv ℝ (fun p => fderiv ℝ (fun p => toMer (H p)) p (0, e)) q (0, e) =
      toMer (fderiv ℝ (fun y => fderiv ℝ (fun y' => H (q.1, y')) y e) q.2 e) := by
  have hev : (fun p => fderiv ℝ (fun p => toMer (H p)) p (0, e)) =ᶠ[𝓝 q]
      fun p => Lm (fderiv ℝ H p (0, e)) := by
    filter_upwards [ev_mem hq] with p hp
    exact dir_toMer _ ((hH p hp).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun p => fderiv ℝ H p (0, e)) q :=
    (dir_cd _ (hH q hq)).differentiableAt one_ne_zero
  have h1 := (Lm.hasFDerivAt.comp q hg.hasFDerivAt).fderiv
  have h2 := congrArg (fun L => L (0, e)) h1
  have h3 : fderiv ℝ (fun p => Lm (fderiv ℝ H p (0, e))) q (0, e)
      = Lm (fderiv ℝ (fun p => fderiv ℝ H p (0, e)) q (0, e)) := h2
  rw [h3, Lm_apply]
  congr 1
  have h4 := slice_fderiv (fun p => fderiv ℝ H p (0, e)) q.1 q.2 e hg
  rw [show (q.1, q.2) = q from rfl] at h4
  rw [← h4]
  congr 2
  funext y
  exact (slice_fderiv H q.1 y e ((hH (q.1, y) hq).differentiableAt (by norm_num))).symm

theorem hp_dc (ν μ : ℝ) {H : Chart → ℝ × ℝ} {q : Chart} (hq : 0 < q.1)
    (hH : ∀ p : Chart, 0 < p.1 → ContDiffAt ℝ 2 H p) :
    Dc ν μ (fun p => toMer (H p)) q =
      toMer (deriv (fun s' => H (s', q.2)) q.1 + (μ / q.1) • H q
        - ν • lapPl (fun y => H (q.1, y)) q.2) := by
  have hd := (hH q hq).differentiableAt (by norm_num)
  have ha : UnforcedLeray.Axi.dS (fun p => toMer (H p)) q
      = toMer (deriv (fun s' => H (s', q.2)) q.1) := by
    unfold UnforcedLeray.Axi.dS
    rw [dir_toMer _ hd, slice_deriv H q.1 q.2 hd]
  have hb : lapQE (fun p => toMer (H p)) q = toMer (lapPl (fun y => H (q.1, y)) q.2) := by
    unfold lapQE UnforcedLeray.Axi.dQ UnforcedLeray.Axi.dEta lapPl
    rw [Fin.sum_univ_two]
    have e0 := dir2_toMer (1, 0) hq hH
    have e1 := dir2_toMer (0, 1) hq hH
    simp only [ei, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [e0, e1, toMer_add]
  rw [Dc, ha, hb]
  simp only [toMer_add, toMer_sub, toMer_smul]

end UnforcedLeray.Short.PartIIIb.Concrete.DcSplitAux

namespace UnforcedLeray.Short.PartIIIb.Concrete

open DcSplitAux in
theorem dcSplit (as : ℝ) (χf : ℝ → ℝ) : DcSplit as χf := by
  intro hχ ν μ ε hν A hA q hq
  obtain ⟨hP, hΨ⟩ := latSmooth as χf hχ ν hν A hA
  set H : Chart → ℝ × ℝ := fun p => hpA ν χf A p.1 p.2 with hHdef
  have hHeq : H = fun p => fromMer (hpM ν χf A p) := by
    funext p; simp [hHdef, hpM, fromMer_toMer]
  have hHc : ContDiffOn ℝ 4 H (Ioi 0 ×ˢ univ) := by
    rw [hHeq]; exact fromMer.contDiff.comp_contDiffOn hP
  have hH2 : ∀ p : Chart, 0 < p.1 → ContDiffAt ℝ 2 H p := fun p hp =>
    (cdAt hHc hp).of_le (by norm_num)
  have hpM2 : ContDiffOn ℝ 2 (hpM ν χf A) (Ioi 0 ×ˢ univ) := hP.of_le (by norm_num)
  -- Θ is C²
  have hK : ContDiffOn ℝ 3 (fun p : Chart => p.2.2 * fderiv ℝ (psiM ν χf A) p (0, (0, 1))
      + 2 * p.1 * fderiv ℝ (psiM ν χf A) p (1, (0, 0))) (Ioi 0 ×ˢ univ) := by
    have d : ContDiffOn ℝ 3 (fun y => fderiv ℝ (psiM ν χf A) y) (Ioi 0 ×ˢ univ) :=
      hΨ.fderiv_of_isOpen openU (by norm_num)
    have d1 := d.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
    have d2 := d.clm_apply (contDiffOn_const (c := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
    exact ((contDiff_snd.comp contDiff_snd).contDiffOn.mul d1).add
      (((contDiffOn_const.mul contDiffOn_fst)).mul d2)
  have hT3 : ContDiffOn ℝ 3 (thetaM ν χf A) (Ioi 0 ×ˢ univ) := by
    have hΨ3 : ContDiffOn ℝ 3 (psiM ν χf A) (Ioi 0 ×ˢ univ) := hΨ.of_le (by norm_num)
    have hc : ContDiffOn ℝ 3 (fun p : Chart => toMer (0, psiM ν χf A p - (p.2.2 *
        fderiv ℝ (psiM ν χf A) p (0, (0, 1)) + 2 * p.1 * fderiv ℝ (psiM ν χf A) p (1, (0, 0)))))
        (Ioi 0 ×ˢ univ) :=
      Lm.contDiff.comp_contDiffOn (contDiffOn_const.prodMk (hΨ3.sub hK))
    refine hc.congr ?_
    intro p hp
    have hd : DifferentiableAt ℝ (psiM ν χf A) p :=
      (cdAt hΨ hp.1).differentiableAt (by norm_num)
    have e1 := slice_fderiv (psiM ν χf A) p.1 p.2 (ei 1) hd
    have e2 := slice_deriv (psiM ν χf A) p.1 p.2 hd
    simp only [thetaM, Kop]
    congr 2
    have e1' : fderiv ℝ (fun y => psipA ν χf A p.1 y) p.2 (ei 1) =
        fderiv ℝ (psiM ν χf A) p (0, (0, 1)) := e1
    have e2' : deriv (fun s' => psipA ν χf A s' p.2) p.1 =
        fderiv ℝ (psiM ν χf A) p (1, (0, 0)) := e2
    rw [e1', e2']
    rfl
  have hT2 : ContDiffOn ℝ 2 (thetaM ν χf A) (Ioi 0 ×ˢ univ) := hT3.of_le (by norm_num)
  have hb : hbM ν ε χf A = hpM ν χf A + ε • thetaM ν χf A := rfl
  rw [hb, dc_add ν μ ε hpM2 hT2 hq]
  have := hp_dc ν μ hq hH2
  have hpe : hpM ν χf A = fun p => toMer (H p) := rfl
  rw [hpe, this]

end UnforcedLeray.Short.PartIIIb.Concrete
