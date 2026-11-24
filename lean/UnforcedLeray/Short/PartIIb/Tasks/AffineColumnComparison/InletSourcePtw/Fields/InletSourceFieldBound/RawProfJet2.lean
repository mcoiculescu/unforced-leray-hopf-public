import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_8
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RawProfileYoungJets

/-!
# Part II-b, task `PartII-b:G4/4/1/1/8/1`: `RawProfJet2`

Source of record: `the November 2 reference manuscript` (SP) lines 2419-2423,
460-478 (`sct:transverse`, `sct:fixed-band`).

Proves `rawProfJet2 : RawProfJet2`: on the slow band `0 < s ≤ H = Σ/ν` in `BgRegime`, the raw
profile `b_raw = (v₁, v₂ + εH)`, `H = (1 - K)ψ`, satisfies
`‖iteratedFDeriv ℝ l (rawProf p) x‖ ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N` for `l ≤ 2`.

Route:
1. All mixed age/space jets `ageJet ℓ j p.train.v` are uniformly bounded by `C * (p.ν ^ K)⁻¹` on
   `0 < s ≤ H` via `vb_single`, `fixedBandJets_of` (`PartI.TrainFixedBand`), and `vcJetSup_proof`.
2. For any stream pair `(ψ, v)`, `fderiv (∂_s^ℓ ψ_s) = perpCLM ∘ (∂_s^ℓ v_s)` (`PsiQSwap`,
   `PsiEtaSwap`), giving `‖ageJet ℓ (k + 1) ψ‖ ≤ 2 ‖ageJet ℓ k v‖` for all `ℓ, k : ℕ`, while
   `ageJet ℓ 0 ψ` is bounded via `tailPsi_part` (`PartI.TrainTransverseTails`) and
   `psiEtaSegment_proof`.
3. `PartI.jointFromAgeJets` converts the mixed jets `ℓ + j ≤ 3` into a uniform bound on
   `‖iteratedFDeriv ℝ j Ψ x‖` (`j ≤ 3`) for `Ψ(s, z) = p.train.ψ s z`.
4. Identifying `rawProf p` on `{s > 0}` with `RawYoung.Gfun p.ε Ψ U` (`bgRawProfile_eq_on`), the
   order-`≤ 2` Leibniz and CLM composition bounds yield `RawProfJet2` with `N = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.Concrete

namespace RawProfJet2Aux

private theorem partI_transverseTails : PartI.TrainTransverseTails :=
  let hFD0 : PartI.OverlapFluctuationDecay :=
    PartI.overlap_fluctuation_decay PartI.overlap_highnorm_uniform
  let hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof hFD0
      (PartI.overlap_mean_decay PartI.overlap_highnorm_uniform hFD0 PartI.overlap_mean_primitive)
  let hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  let hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  PartI.trainTransverseTails_proof hVort hTails

private theorem partI_fixedBand : PartI.TrainFixedBand :=
  let hFD0 : PartI.OverlapFluctuationDecay :=
    PartI.overlap_fluctuation_decay PartI.overlap_highnorm_uniform
  let hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof hFD0
      (PartI.overlap_mean_decay PartI.overlap_highnorm_uniform hFD0 PartI.overlap_mean_primitive)
  let hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  let hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  let hFD : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  PartI.trainFixedBand_proof hTails hFD

private theorem inv_pow_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (ν ^ a)⁻¹ ≤ (ν ^ b)⁻¹ :=
  inv_anti₀ (pow_pos hν b) (pow_le_pow_of_le_one hν.le hν1 hab)

/-- Uniform bound on every mixed age/space jet `(ℓ, j)` of `p.train.v` on `0 < s ≤ p.H`. -/
private theorem vel_ageJet_bound {Sig : ℝ} (hSig : 0 < Sig) (dm dp : ℝ) (ℓ j : ℕ) :
    ∃ (C : ℝ) (K : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
        ∀ (s : ℝ), 0 < s → s ≤ p.H → ∀ z : UnforcedLeray.Cyl.Plane,
          ‖PartI.ageJet ℓ j p.train.v s z‖ ≤ C * (p.ν ^ K)⁻¹ := by
  obtain ⟨Cf, Nf, νf, hCf, hνf, Hf⟩ := (fixedBandJets_of partI_fixedBand) Sig hSig ℓ j
  obtain ⟨Cv, Mv, νv, hCv, hνv, Hv⟩ := vcJetSup_proof Sig hSig ℓ j
  set ν₀ : ℝ := min (min νf νv) 1
  have hν₀ : 0 < ν₀ := lt_min (lt_min hνf hνv) one_pos
  have hν₀1 : ν₀ ≤ 1 := min_le_right _ _
  refine ⟨Cf + Cv, max Nf Mv, ν₀, add_pos hCf hCv, hν₀, hν₀1, ?_⟩
  intro p d hd hν hS s hs hsH z
  exact vb_single trainVelSmooth_proof vcSmooth_proof ℓ j hν₀ hν₀1 hCf.le hCv.le
    (le_max_left _ _) (le_max_right _ _)
    (fun ν hν0 hνle tr htr s' hs' hsSig z' =>
      Hf ν hν0 (hνle.trans ((min_le_left _ _).trans (min_le_left _ _))) tr htr s' hs' hsSig z')
    (fun ν hν0 hνle s' hs' hsSig z' =>
      Hv ν hν0 (hνle.trans ((min_le_left _ _).trans (min_le_right _ _))) s' hs' hsSig z')
    p d dm dp hd hν hS s hs hsH z

/-- Continuous linear map sending `u = (u₀, u₁)` to the linear form `h ↦ h₁ u₁ - h₂ u₀`. -/
private def perpCLM : UnforcedLeray.Train.Vec →L[ℝ] (UnforcedLeray.Cyl.Plane →L[ℝ] ℝ) :=
  ContinuousLinearMap.smulRight (EuclideanSpace.proj (1 : Fin 2))
      (ContinuousLinearMap.fst ℝ ℝ ℝ) -
    ContinuousLinearMap.smulRight (EuclideanSpace.proj (0 : Fin 2))
      (ContinuousLinearMap.snd ℝ ℝ ℝ)

private lemma perpCLM_apply (u : UnforcedLeray.Train.Vec) (h : UnforcedLeray.Cyl.Plane) :
    perpCLM u h = h.1 * u 1 - h.2 * u 0 := by
  change u 1 * h.1 - u 0 * h.2 = h.1 * u 1 - h.2 * u 0
  ring

private lemma norm_perpCLM_le : ‖perpCLM‖ ≤ 2 := by
  refine perpCLM.opNorm_le_bound (by norm_num) fun u => ?_
  refine (perpCLM u).opNorm_le_bound (mul_nonneg (by norm_num) (norm_nonneg u)) fun h => ?_
  rw [perpCLM_apply, Real.norm_eq_abs]
  have hu0 : |u 0| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le u 0
  have hu1 : |u 1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le u 1
  have hh1 : |h.1| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le h
  have hh2 : |h.2| ≤ ‖h‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le h
  have e1 : |h.1 * u 1| ≤ ‖h‖ * ‖u‖ := by
    rw [abs_mul]; exact mul_le_mul hh1 hu1 (abs_nonneg _) (norm_nonneg _)
  have e2 : |h.2 * u 0| ≤ ‖h‖ * ‖u‖ := by
    rw [abs_mul]; exact mul_le_mul hh2 hu0 (abs_nonneg _) (norm_nonneg _)
  have e3 := abs_sub (h.1 * u 1) (h.2 * u 0)
  nlinarith

/-- Spatial derivatives of `∂_s^ℓ ψ` of order `k + 1` are controlled by order-`k` derivatives of
`∂_s^ℓ v` for any stream pair `(ψ, v)`. -/
private lemma psi_ageJet_succ_le {ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ}
    {v : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec}
    (hsp : IsStreamPair ψ v) (ℓ k : ℕ) {s : ℝ} (hs : 0 < s) (z : UnforcedLeray.Cyl.Plane) :
    ‖PartI.ageJet ℓ (k + 1) ψ s z‖ ≤ 2 * ‖PartI.ageJet ℓ k v s z‖ := by
  set g : UnforcedLeray.Cyl.Plane → ℝ := fun w => iteratedDeriv ℓ (fun r => ψ r w) s
  set u : UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec :=
    fun w => iteratedDeriv ℓ (fun r => v r w) s
  have hfd_eq : fderiv ℝ g = perpCLM ∘ u := by
    funext ⟨q, η⟩
    have hg1 : ContDiffAt ℝ (1 : ℕ) g (q, η) :=
      vb_slice_contDiffAt (fun x : ℝ × UnforcedLeray.Cyl.Plane => ψ x.1 x.2) hsp.1 ℓ 1 hs (q, η)
    have hgd : DifferentiableAt ℝ g (q, η) := hg1.differentiableAt (by norm_num)
    have h10' : HasDerivAt (g ∘ fun q' => (q', η)) (fderiv ℝ g (q, η) (1, 0)) q :=
      hgd.hasFDerivAt.comp_hasDerivAt q ((hasDerivAt_id' q).prodMk (hasDerivAt_const q η))
    have h10 : fderiv ℝ g (q, η) (1, 0) = u (q, η) 1 :=
      h10'.unique (psiQSwap_proof ψ v hsp ℓ s hs q η)
    have h01' : HasDerivAt (g ∘ fun η' => (q, η')) (fderiv ℝ g (q, η) (0, 1)) η :=
      hgd.hasFDerivAt.comp_hasDerivAt η ((hasDerivAt_const η q).prodMk (hasDerivAt_id' η))
    have h01 : fderiv ℝ g (q, η) (0, 1) = -(u (q, η) 0) :=
      h01'.unique (psiEtaSwap_proof ψ v hsp ℓ s hs q η)
    apply ContinuousLinearMap.ext
    intro h
    have hdec : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    change fderiv ℝ g (q, η) h = perpCLM (u (q, η)) h
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, map_smul, h10, h01, smul_eq_mul, smul_eq_mul, perpCLM_apply]
    ring
  have hu_cd : ContDiffAt ℝ (k : ℕ) u z :=
    vb_slice_contDiffAt (fun x : ℝ × UnforcedLeray.Cyl.Plane => v x.1 x.2) hsp.2.1 ℓ k hs z
  have h1 : ‖PartI.ageJet ℓ (k + 1) ψ s z‖ = ‖iteratedFDeriv ℝ k (fderiv ℝ g) z‖ := by
    change ‖iteratedFDeriv ℝ (k + 1) g z‖ = _
    exact norm_iteratedFDeriv_fderiv.symm
  have h2 : ‖iteratedFDeriv ℝ k (perpCLM ∘ u) z‖ ≤ ‖perpCLM‖ * ‖iteratedFDeriv ℝ k u z‖ :=
    perpCLM.norm_iteratedFDeriv_comp_left hu_cd le_rfl
  rw [h1, hfd_eq]
  calc ‖iteratedFDeriv ℝ k (perpCLM ∘ u) z‖
      ≤ ‖perpCLM‖ * ‖iteratedFDeriv ℝ k u z‖ := h2
    _ ≤ 2 * ‖PartI.ageJet ℓ k v s z‖ :=
        mul_le_mul_of_nonneg_right norm_perpCLM_le (norm_nonneg _)

/-- Uniform bound on every mixed age/space jet `(ℓ, j)` of `p.train.ψ` on `0 < s ≤ p.H`. -/
private theorem psi_ageJet_bound {Sig : ℝ} (hSig : 0 < Sig) (dm dp : ℝ) (ℓ j : ℕ) :
    ∃ (C : ℝ) (K : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
        ∀ (s : ℝ), 0 < s → s ≤ p.H → ∀ z : UnforcedLeray.Cyl.Plane,
          ‖PartI.ageJet ℓ j p.train.ψ s z‖ ≤ C * (p.ν ^ K)⁻¹ := by
  cases j with
  | zero =>
    obtain ⟨Cp, CT, NT, νT, hCp, hCT, hνT, HT⟩ := tailPsi_part partI_transverseTails ℓ
    obtain ⟨Cv, Kv, νv, hCv, hνv, hνv1, Hv⟩ := vel_ageJet_bound hSig dm dp ℓ 0
    set Ct : ℝ := 2 * (CT * (3 * (1 + Sig)) ^ NT)
    have hCt : 0 < Ct := by positivity
    set K : ℕ := max (3 * NT) Kv + 1
    set ν₀ : ℝ := min νT νv
    have hν₀ : 0 < ν₀ := lt_min hνT hνv
    have hν₀1 : ν₀ ≤ 1 := (min_le_right _ _).trans hνv1
    refine ⟨Ct + 2 * (Cp + 2) * Cv, K, ν₀, by positivity, hν₀, hν₀1, ?_⟩
    intro p d hd hν hS s hs hsH z
    have hνp : 0 < p.ν := p.ν_pos
    have hν1 : p.ν ≤ 1 := hν.trans hν₀1
    have hνT' : p.ν ≤ νT := hν.trans (min_le_left _ _)
    have hνv' : p.ν ≤ νv := hν.trans (min_le_right _ _)
    have hH : p.H = Sig / p.ν := by
      unfold UnforcedLeray.Cons.C03.Concrete.Params.H; rw [hS]
    have hsSig : s ≤ Sig / p.ν := hH ▸ hsH
    have hSig0 : 0 ≤ Sig / p.ν := div_nonneg hSig.le hνp.le
    have htail : ∀ w : UnforcedLeray.Cyl.Plane, Cp / p.ν + 2 ≤ |w.2| →
        ‖PartI.ageJet ℓ 0 p.train.ψ s w‖ ≤ Ct * (p.ν ^ K)⁻¹ := by
      intro w hw
      have e1 := HT p.ν hνp hνT' p.c hd.c_eq p.train hd.train_buc (Sig / p.ν) hSig0 s hs hsSig w hw
      have e2 := polyPS_tail_le CT NT K hCT.le
        ((le_max_left _ _).trans (Nat.le_succ _)) hνp hν1 hSig.le
      rw [← hd.c_eq] at e2
      exact e1.trans e2
    by_cases hcase : Cp / p.ν + 2 ≤ |z.2|
    · refine (htail z hcase).trans ?_
      have : 0 ≤ 2 * (Cp + 2) * Cv * (p.ν ^ K)⁻¹ := by positivity
      linarith
    · have hlt : |z.2| < Cp / p.ν + 2 := lt_of_not_ge hcase
      set b : ℝ := Cp / p.ν + 2
      have hbpos : 0 < b := by positivity
      have htb := htail (z.1, b) (by show Cp / p.ν + 2 ≤ |b|; rw [abs_of_pos hbpos])
      have hsp : IsStreamPair p.train.ψ p.train.v :=
        ⟨hd.train_stream_smooth, trainVelSmooth_proof p d dm dp hd,
          fun s' hs' z' => p.train.isTrain.stream s' hs'.le z'⟩
      have hseg := psiEtaSegment_proof p.train.ψ p.train.v hsp ℓ s hs z.1 z.2 b
        (Cv * (p.ν ^ Kv)⁻¹) (fun t _ => Hv p d hd hνv' hS s hs hsH (z.1, t))
      have hab : |z.2 - b| ≤ 2 * (Cp + 2) * p.ν⁻¹ := by
        have h1 : |z.2 - b| ≤ |z.2| + |b| := abs_sub _ _
        rw [abs_of_pos hbpos] at h1
        have hinv : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνp).2 hν1
        have hdiv : Cp / p.ν = Cp * p.ν⁻¹ := div_eq_mul_inv _ _
        nlinarith
      have hKvK : p.ν⁻¹ * (p.ν ^ Kv)⁻¹ ≤ (p.ν ^ K)⁻¹ := by
        have heq : p.ν⁻¹ * (p.ν ^ Kv)⁻¹ = (p.ν ^ (Kv + 1))⁻¹ := by
          rw [pow_succ, mul_inv, mul_comm]
        rw [heq]
        exact inv_pow_mono hνp hν1 (Nat.succ_le_succ (le_max_right _ _))
      have hprod : Cv * (p.ν ^ Kv)⁻¹ * |z.2 - b| ≤ 2 * (Cp + 2) * Cv * (p.ν ^ K)⁻¹ := by
        calc Cv * (p.ν ^ Kv)⁻¹ * |z.2 - b|
            ≤ Cv * (p.ν ^ Kv)⁻¹ * (2 * (Cp + 2) * p.ν⁻¹) :=
              mul_le_mul_of_nonneg_left hab (by positivity)
          _ = 2 * (Cp + 2) * Cv * (p.ν⁻¹ * (p.ν ^ Kv)⁻¹) := by ring
          _ ≤ 2 * (Cp + 2) * Cv * (p.ν ^ K)⁻¹ :=
              mul_le_mul_of_nonneg_left hKvK (by positivity)
      have hz : (z.1, z.2) = z := Prod.mk.eta
      rw [hz] at hseg
      linarith [htb, hseg, hprod]
  | succ k =>
    obtain ⟨Cv, Kv, νv, hCv, hνv, hνv1, Hv⟩ := vel_ageJet_bound hSig dm dp ℓ k
    refine ⟨2 * Cv, Kv, νv, by positivity, hνv, hνv1, ?_⟩
    intro p d hd hν hS s hs hsH z
    have hsp : IsStreamPair p.train.ψ p.train.v :=
      ⟨hd.train_stream_smooth, trainVelSmooth_proof p d dm dp hd,
        fun s' hs' z' => p.train.isTrain.stream s' hs'.le z'⟩
    calc ‖PartI.ageJet ℓ (k + 1) p.train.ψ s z‖
        ≤ 2 * ‖PartI.ageJet ℓ k p.train.v s z‖ := psi_ageJet_succ_le hsp ℓ k hs z
      _ ≤ 2 * (Cv * (p.ν ^ Kv)⁻¹) :=
          mul_le_mul_of_nonneg_left (Hv p d hd hν hS s hs hsH z) zero_le_two
      _ = (2 * Cv) * (p.ν ^ Kv)⁻¹ := by ring

/-- Joint spacetime derivatives of `p.train.ψ` up to order `≤ 3` on `0 < s ≤ p.H`. -/
private theorem psi_joint_bound {Sig : ℝ} (hSig : 0 < Sig) (dm dp : ℝ) :
    ∃ (CΨ : ℝ) (KΨ : ℕ) (ν₀ : ℝ), 0 < CΨ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H → ∀ j ≤ 3,
          ‖iteratedFDeriv ℝ j (fun y : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ y.1 y.2) x‖ ≤
            CΨ * (p.ν ^ KΨ)⁻¹ := by
  choose Cq Kq νq hCq hνq hνq1 Hq using
    fun q : Fin 4 × Fin 4 => psi_ageJet_bound hSig dm dp q.1.1 q.2.1
  choose KJ hKJ0 hKJ using UnforcedLeray.Short.PartI.jointFromAgeJets
  set Call : ℝ := 1 + ∑ q : Fin 4 × Fin 4, Cq q
  set Kall : ℕ := ∑ q : Fin 4 × Fin 4, Kq q
  set ν₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty νq
  set KJmax : ℝ := 1 + ∑ j ∈ Finset.range 4, KJ j
  have hCall : 0 < Call := add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun q _ => (hCq q).le)
  have hKJmax : 0 < KJmax := add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun j _ => hKJ0 j)
  have hν₀ : 0 < ν₀ := (Finset.lt_inf'_iff _).2 fun q _ => hνq q
  have hν₀1 : ν₀ ≤ 1 :=
    (Finset.inf'_le _ (Finset.mem_univ ((0 : Fin 4), (0 : Fin 4)))).trans (hνq1 _)
  refine ⟨KJmax * (4 * Call), Kall, ν₀, by positivity, hν₀, hν₀1, ?_⟩
  intro p d hd hν hS x hx0 hxH j hj
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans hν₀1
  have hstep := hKJ j p.train.ψ hd.train_stream_smooth x hx0
  have hsum : ∑ ℓ ∈ Finset.range (j + 1), ‖PartI.ageJet ℓ (j - ℓ) p.train.ψ x.1 x.2‖ ≤
      4 * (Call * (p.ν ^ Kall)⁻¹) := by
    calc ∑ ℓ ∈ Finset.range (j + 1), ‖PartI.ageJet ℓ (j - ℓ) p.train.ψ x.1 x.2‖
        ≤ ∑ _ℓ ∈ Finset.range (j + 1), Call * (p.ν ^ Kall)⁻¹ := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          have hℓlt : ℓ < 4 := by have := Finset.mem_range.1 hℓ; omega
          have hjlt : j - ℓ < 4 := by omega
          let q : Fin 4 × Fin 4 := (⟨ℓ, hℓlt⟩, ⟨j - ℓ, hjlt⟩)
          have hνq' : p.ν ≤ νq q := hν.trans (Finset.inf'_le _ (Finset.mem_univ q))
          have h1 := Hq q p d hd hνq' hS x.1 hx0 hxH x.2
          have hC_le : Cq q ≤ Call := by
            have : Cq q ≤ ∑ q' : Fin 4 × Fin 4, Cq q' :=
              Finset.single_le_sum (fun q' _ => (hCq q').le) (Finset.mem_univ q)
            linarith
          have hK_le : Kq q ≤ Kall :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
          calc ‖PartI.ageJet ℓ (j - ℓ) p.train.ψ x.1 x.2‖
              ≤ Cq q * (p.ν ^ Kq q)⁻¹ := h1
            _ ≤ Call * (p.ν ^ Kall)⁻¹ :=
                mul_le_mul hC_le (inv_pow_mono hνp hν1 hK_le) (by positivity) hCall.le
      _ = ((j + 1 : ℕ) : ℝ) * (Call * (p.ν ^ Kall)⁻¹) := by simp
      _ ≤ 4 * (Call * (p.ν ^ Kall)⁻¹) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show j + 1 ≤ 4 by omega)
  have hKJj : KJ j ≤ KJmax := by
    have : KJ j ≤ ∑ m ∈ Finset.range 4, KJ m :=
      Finset.single_le_sum (fun m _ => hKJ0 m) (Finset.mem_range.2 (by omega))
    linarith
  calc ‖iteratedFDeriv ℝ j (fun y : ℝ × UnforcedLeray.Cyl.Plane => p.train.ψ y.1 y.2) x‖
      ≤ KJ j * ∑ ℓ ∈ Finset.range (j + 1), ‖PartI.ageJet ℓ (j - ℓ) p.train.ψ x.1 x.2‖ := hstep
    _ ≤ KJmax * (4 * (Call * (p.ν ^ Kall)⁻¹)) :=
        mul_le_mul hKJj hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _) hKJmax.le
    _ = KJmax * (4 * Call) * (p.ν ^ Kall)⁻¹ := by ring

/-- Unweighted Leibniz bound up to order `≤ 2` on an open set. -/
private lemma prod_le2 {f g : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ i ≤ 2, ‖iteratedFDerivWithin ℝ i f U x‖ ≤ A)
    (hgb : ∀ k ≤ 2, ‖iteratedFDerivWithin ℝ k g U x‖ ≤ B) {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDerivWithin ℝ n (fun y => f y * g y) U x‖ ≤ 4 * A * B := by
  have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hf hg hU.uniqueDiffOn hx
    (n := n) (by simp)
  have hab : ∀ i ≤ 2, ∀ k ≤ 2,
      ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ k g U x‖ ≤ A * B :=
    fun i hi k hk => mul_le_mul (hfb i hi) (hgb k hk) (norm_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  interval_cases n
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
      Nat.cast_one, one_mul] at hmul
    nlinarith [hab 0 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, Nat.reduceSub, one_mul] at hmul
    nlinarith [hab 0 (by norm_num) 1 (by norm_num), hab 1 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub,
      one_mul] at hmul
    nlinarith [hab 0 (by norm_num) 2 (by norm_num), hab 1 (by norm_num) 1 (by norm_num),
      hab 2 (by norm_num) 0 (by norm_num)]

end RawProfJet2Aux

/-- **Task `PartII-b:G4/4/1/1/8/1`** (`RawProfJet2`, SP 2419-2423, 460-478): jets of order `≤ 2`
of the raw profile `rawProf p` on `0 < s ≤ H = Σ/ν` are bounded by `C ν^{-k} (1 + |η|)^N`. -/
theorem rawProfJet2 : UnforcedLeray.Short.IIb.RawProfJet2 := by
  intro Sig hSig dm dp _hdm
  obtain ⟨CΨ, KΨ, ν₀, hCΨ, hν₀, hν₀1, HΨ⟩ := RawProfJet2Aux.psi_joint_bound hSig dm dp
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  obtain ⟨Kη, hKη0, hKη⟩ := RawYoung.coord_eta hU
  set Ks : ℝ := 2 * Sig + ‖RawYoung.L2‖ + 1
  have hKs0 : 0 < Ks := by linarith [norm_nonneg RawYoung.L2]
  set c01 : ℝ := ‖ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))‖
  set c10 : ℝ := ‖ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖
  set C : ℝ := (‖RawYoung.rawLam‖ + ‖RawYoung.smulE‖ * (1 + 4 * Kη * c01 + 4 * Ks * c10) + 1) * CΨ
  refine ⟨C, KΨ + 1, 1, ν₀, by positivity, hν₀, ?_⟩
  intro p d hreg hν hS x hx0 hxH l hl
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans hν₀1
  have hu1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνp).2 hν1
  have hw1 : (1 : ℝ) ≤ 1 + |x.2.2| := by linarith [abs_nonneg x.2.2]
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff, neg_div]
    have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνp.le
    linarith
  have hεn : ‖p.ε‖ ≤ 1 := by rwa [Real.norm_of_nonneg hε0]
  have hxU : x ∈ U := ⟨hx0, trivial⟩
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun y => p.train.ψ y.1 y.2
  have hΨ : ContDiffOn ℝ ∞ Ψ U := hreg.train_stream_smooth
  set M₀ : ℝ := CΨ * (p.ν ^ KΨ)⁻¹
  have hM₀ : 0 ≤ M₀ := by positivity
  have hΨb : ∀ j ≤ 3, (1 : ℝ) ^ 3 * ‖iteratedFDerivWithin ℝ j Ψ U x‖ ≤ M₀ := by
    intro j hj
    rw [one_pow, one_mul, iteratedFDerivWithin_of_isOpen j hU hxU]
    exact HΨ p d hreg hν hS x hx0 hxH j hj
  have hPl : ‖iteratedFDerivWithin ℝ l (fun y => RawYoung.rawLam (fderivWithin ℝ Ψ U y)) U x‖ ≤
      ‖RawYoung.rawLam‖ * M₀ := by
    simpa only [one_pow, one_mul] using RawYoung.comp_bound hU hΨ RawYoung.rawLam hxU le_rfl hΨb hl
  have ha : ∀ k ≤ 2, ‖iteratedFDerivWithin ℝ k
      (fun y => fderivWithin ℝ Ψ U y (0, (0, 1))) U x‖ ≤ c01 * M₀ := fun k hk => by
    have h := RawYoung.comp_bound hU hΨ
      (ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))) hxU le_rfl hΨb hk
    rw [one_pow, one_mul] at h
    exact h
  have hc : ∀ k ≤ 2, ‖iteratedFDerivWithin ℝ k
      (fun y => fderivWithin ℝ Ψ U y (1, (0, 0))) U x‖ ≤ c10 * M₀ := fun k hk => by
    have h := RawYoung.comp_bound hU hΨ
      (ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))) hxU le_rfl hΨb hk
    rw [one_pow, one_mul] at h
    exact h
  have hsx : x.1 ≤ Sig * p.ν⁻¹ := by
    have hH : p.H = Sig / p.ν := by unfold UnforcedLeray.Cons.C03.Concrete.Params.H; rw [hS]
    rw [← div_eq_mul_inv, ← hH]; exact hxH
  have h2s : ∀ i ≤ 2,
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ × (ℝ × ℝ) => 2 * y.1) U x‖ ≤ Ks * p.ν⁻¹ := by
    intro i hi
    have hL2 : ‖RawYoung.L2‖ ≤ Ks * p.ν⁻¹ := by
      calc ‖RawYoung.L2‖ ≤ ‖RawYoung.L2‖ * p.ν⁻¹ := le_mul_of_one_le_right (norm_nonneg _) hu1
        _ ≤ Ks * p.ν⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hval : |RawYoung.L2 x| ≤ (Ks * p.ν⁻¹) * 1 := by
      have h2 : RawYoung.L2 x = 2 * x.1 := by simp [RawYoung.L2, RawYoung.L1]
      rw [h2, abs_of_pos (by linarith), mul_one]
      have : 2 * x.1 ≤ 2 * Sig * p.ν⁻¹ := by nlinarith
      have : 2 * Sig * p.ν⁻¹ ≤ Ks * p.ν⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith [norm_nonneg RawYoung.L2]) (by positivity)
      linarith
    have hfun : (fun y : ℝ × (ℝ × ℝ) => 2 * y.1) = (fun y => RawYoung.L2 y) := by
      ext y; simp [RawYoung.L2, RawYoung.L1]
    rw [hfun]
    have hcb := RawYoung.coord_bound (L := RawYoung.L2) hU hxU (by positivity) hL2 le_rfl hval hi
    rwa [mul_one] at hcb
  have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ Ψ U) U := hΨ.fderivWithin hU.uniqueDiffOn (by simp)
  have hva : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => fderivWithin ℝ Ψ U y (0, (0, 1))) U :=
    hD.clm_apply contDiffOn_const
  have hvc : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => fderivWithin ℝ Ψ U y (1, (0, 0))) U :=
    hD.clm_apply contDiffOn_const
  have hη_s : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => y.2.2) U := contDiffOn_snd.snd
  have hs_s : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => 2 * y.1) U :=
    contDiffOn_const.mul contDiffOn_fst
  have hTa : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1))) U := hη_s.mul hva
  have hTc : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))) U := hs_s.mul hvc
  have hTt : ContDiffOn ℝ ∞ (RawYoung.Tt Ψ U) U := hTa.add hTc
  have hΦ : ContDiffOn ℝ ∞ (RawYoung.Phi Ψ U) U := hΨ.sub hTt
  have hP : ContDiffOn ℝ ∞ (fun y => RawYoung.rawLam (fderivWithin ℝ Ψ U y)) U :=
    RawYoung.rawLam.contDiff.comp_contDiffOn hD
  have hQ : ContDiffOn ℝ ∞ (fun y => RawYoung.smulE (p.ε * RawYoung.Phi Ψ U y)) U :=
    RawYoung.smulE.contDiff.comp_contDiffOn (contDiffOn_const.mul hΦ)
  have hpa : ‖iteratedFDerivWithin ℝ l
      (fun y : ℝ × (ℝ × ℝ) => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1))) U x‖ ≤
        4 * (Kη * (1 + |x.2.2|)) * (c01 * M₀) :=
    RawProfJet2Aux.prod_le2 hU hη_s hva hxU (by positivity) (by positivity) (hKη x hxU) ha hl
  have hpc : ‖iteratedFDerivWithin ℝ l
      (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))) U x‖ ≤
        4 * (Ks * p.ν⁻¹) * (c10 * M₀) :=
    RawProfJet2Aux.prod_le2 hU hs_s hvc hxU (by positivity) (by positivity) h2s hc hl
  have hΨl : ‖iteratedFDerivWithin ℝ l Ψ U x‖ ≤ M₀ := by
    simpa only [one_pow, one_mul] using hΨb l (hl.trans (by norm_num))
  have hΦl : ‖iteratedFDerivWithin ℝ l (RawYoung.Phi Ψ U) U x‖ ≤
      (1 + 4 * Kη * c01 + 4 * Ks * c10) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by
    have he1 : M₀ ≤ M₀ * p.ν⁻¹ * (1 + |x.2.2|) := by
      have : 1 ≤ p.ν⁻¹ * (1 + |x.2.2|) := one_le_mul_of_one_le_of_one_le hu1 hw1
      calc M₀ = M₀ * 1 := (mul_one _).symm
        _ ≤ M₀ * (p.ν⁻¹ * (1 + |x.2.2|)) := mul_le_mul_of_nonneg_left this hM₀
        _ = M₀ * p.ν⁻¹ * (1 + |x.2.2|) := by ring
    have he2 : 4 * (Kη * (1 + |x.2.2|)) * (c01 * M₀) ≤
        (4 * Kη * c01) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by
      have : 4 * Kη * c01 * M₀ * (1 + |x.2.2|) ≤
          4 * Kη * c01 * M₀ * (1 + |x.2.2|) * p.ν⁻¹ :=
        le_mul_of_one_le_right (by positivity) hu1
      linarith
    have he3 : 4 * (Ks * p.ν⁻¹) * (c10 * M₀) ≤
        (4 * Ks * c10) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by
      have : 4 * Ks * c10 * M₀ * p.ν⁻¹ ≤
          4 * Ks * c10 * M₀ * p.ν⁻¹ * (1 + |x.2.2|) :=
        le_mul_of_one_le_right (by positivity) hw1
      linarith
    calc ‖iteratedFDerivWithin ℝ l (RawYoung.Phi Ψ U) U x‖
        ≤ ‖iteratedFDerivWithin ℝ l Ψ U x‖ +
            ‖iteratedFDerivWithin ℝ l (RawYoung.Tt Ψ U) U x‖ :=
          RawYoung.iter_sub_le hU hΨ hTt hxU l
      _ ≤ ‖iteratedFDerivWithin ℝ l Ψ U x‖ +
            (‖iteratedFDerivWithin ℝ l
                (fun y : ℝ × (ℝ × ℝ) => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1))) U x‖ +
              ‖iteratedFDerivWithin ℝ l
                (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))) U x‖) :=
          add_le_add le_rfl (RawYoung.iter_add_le hU hTa hTc hxU l)
      _ ≤ (1 + 4 * Kη * c01 + 4 * Ks * c10) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by
          linarith [hΨl, hpa, hpc, he1, he2, he3]
  have hQl : ‖iteratedFDerivWithin ℝ l (fun y => RawYoung.smulE (p.ε * RawYoung.Phi Ψ U y)) U x‖ ≤
      ‖RawYoung.smulE‖ * ((1 + 4 * Kη * c01 + 4 * Ks * c10) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|))) := by
    have h1 := RawYoung.smulE_comp_bound (c := fun y => p.ε * RawYoung.Phi Ψ U y) hU
      (contDiffOn_const.mul hΦ) hxU l
    have h2 := RawYoung.iter_const_mul hU hΦ p.ε hxU l
    have h3 : ‖p.ε‖ * ‖iteratedFDerivWithin ℝ l (RawYoung.Phi Ψ U) U x‖ ≤
        (1 + 4 * Kη * c01 + 4 * Ks * c10) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by
      calc ‖p.ε‖ * ‖iteratedFDerivWithin ℝ l (RawYoung.Phi Ψ U) U x‖
          ≤ 1 * ‖iteratedFDerivWithin ℝ l (RawYoung.Phi Ψ U) U x‖ :=
            mul_le_mul_of_nonneg_right hεn (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hΦl
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg _))
  have hEq : EqOn (rawProf p) (RawYoung.Gfun p.ε Ψ U) U := by
    intro y hy
    unfold rawProf
    rw [bgRawProfile_eq_on hreg hy]
    simp only [RawYoung.Gfun, RawYoung.Phi, RawYoung.Tt, RawYoung.rawLam_apply,
      RawYoung.smulE_apply, fderivWithin_of_isOpen hU hy]
    rfl
  rw [← iteratedFDerivWithin_of_isOpen l hU hxU, iteratedFDerivWithin_congr hEq hxU l]
  have hPl' : ‖RawYoung.rawLam‖ * M₀ ≤
      ‖RawYoung.rawLam‖ * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by
    have : 1 ≤ p.ν⁻¹ * (1 + |x.2.2|) := one_le_mul_of_one_le_of_one_le hu1 hw1
    calc ‖RawYoung.rawLam‖ * M₀ = ‖RawYoung.rawLam‖ * M₀ * 1 := (mul_one _).symm
      _ ≤ ‖RawYoung.rawLam‖ * M₀ * (p.ν⁻¹ * (1 + |x.2.2|)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ‖RawYoung.rawLam‖ * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) := by ring
  have hMpow : M₀ * p.ν⁻¹ = CΨ * (p.ν ^ (KΨ + 1))⁻¹ := by
    simp only [M₀, pow_succ, mul_inv]
    ring
  have hextra : 0 ≤ CΨ * (p.ν ^ (KΨ + 1))⁻¹ * (1 + |x.2.2|) := by positivity
  rw [pow_one]
  calc ‖iteratedFDerivWithin ℝ l (RawYoung.Gfun p.ε Ψ U) U x‖
      ≤ ‖iteratedFDerivWithin ℝ l (fun y => RawYoung.rawLam (fderivWithin ℝ Ψ U y)) U x‖ +
          ‖iteratedFDerivWithin ℝ l (fun y => RawYoung.smulE (p.ε * RawYoung.Phi Ψ U y)) U x‖ :=
        RawYoung.iter_add_le hU hP hQ hxU l
    _ ≤ ‖RawYoung.rawLam‖ * (M₀ * p.ν⁻¹ * (1 + |x.2.2|)) +
          ‖RawYoung.smulE‖ *
            ((1 + 4 * Kη * c01 + 4 * Ks * c10) * (M₀ * p.ν⁻¹ * (1 + |x.2.2|))) := by
        linarith [hPl, hPl', hQl]
    _ = (‖RawYoung.rawLam‖ + ‖RawYoung.smulE‖ * (1 + 4 * Kη * c01 + 4 * Ks * c10)) *
          ((M₀ * p.ν⁻¹) * (1 + |x.2.2|)) := by ring
    _ = (‖RawYoung.rawLam‖ + ‖RawYoung.smulE‖ * (1 + 4 * Kη * c01 + 4 * Ks * c10)) *
          (CΨ * (p.ν ^ (KΨ + 1))⁻¹ * (1 + |x.2.2|)) := by rw [hMpow]
    _ ≤ C * (p.ν ^ (KΨ + 1))⁻¹ * (1 + |x.2.2|) := by
        have : C * (p.ν ^ (KΨ + 1))⁻¹ * (1 + |x.2.2|) =
            (‖RawYoung.rawLam‖ + ‖RawYoung.smulE‖ * (1 + 4 * Kη * c01 + 4 * Ks * c10)) *
              (CΨ * (p.ν ^ (KΨ + 1))⁻¹ * (1 + |x.2.2|)) +
            CΨ * (p.ν ^ (KΨ + 1))⁻¹ * (1 + |x.2.2|) := by
          dsimp only [C]; ring
        linarith

end UnforcedLeray.Short.IIb

end
