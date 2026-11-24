import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellInterpSmooth

/-!
# `KTSource`: the localized source `f B_l` is in `L¹ ∩ L²` of the cell

Source: `the November 2 reference manuscript` lines 3052-3058.
With `s = (m+1)/2`, `jb = 1 + x₁² + x₂²`, the cell has `jb ≤ (1 + c²/4)(1 + x₂²)`, so the
coefficient bound gives `|B_l| ≤ A₁ jb^{-s}` on the cell.  Then `|f B_l| ≤ A₁ jb^{-s} |f|`:
the `L²` norm is bounded by `jb^{-m/2} |f|` (as `jb^{-1/2} ≤ 1`), and the `L¹` norm by the
weighted Cauchy-Schwarz pairing of `jb^{-s}` (in `X_{m,c}`, since `jb^{-1}` is integrable on the
cell) with `|f|` (in `X_{-m,c}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

open UnforcedLeray UnforcedLeray.Short.IIIa

theorem ktSrc_one_le_jb (x : ℝ × ℝ) : 1 ≤ B0579.jb x := by
  unfold B0579.jb
  nlinarith [sq_nonneg x.1, sq_nonneg x.2]

theorem ktSrc_jb_le (c : ℝ) (x : ℝ × ℝ) (hx : x ∈ B0579.cell c) :
    B0579.jb x ≤ (1 + c ^ 2 / 4) * (1 + x.2 ^ 2) := by
  have hx1 : x.1 ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ c / 2 - x.1 by linarith [hx.1.2])
      (show (0:ℝ) ≤ x.1 + c / 2 by linarith [hx.1.1])]
  unfold B0579.jb
  nlinarith [sq_nonneg x.2, mul_nonneg (sq_nonneg c) (sq_nonneg x.2)]

theorem ktSrc_rpow_bound {K u v s : ℝ} (hK : 0 < K) (hu : 0 < u) (hv : 0 < v)
    (hvK : v ≤ K * u) (hs : 0 ≤ s) : u ^ (-s) ≤ K ^ s * v ^ (-s) := by
  have h1 : (K * u) ^ (-s) ≤ v ^ (-s) := Real.rpow_le_rpow_of_nonpos hv hvK (by linarith)
  rw [Real.mul_rpow hK.le hu.le] at h1
  have h2 : K ^ s * K ^ (-s) = 1 := by
    rw [← Real.rpow_add hK]
    simp
  calc u ^ (-s) = K ^ s * (K ^ (-s) * u ^ (-s)) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ K ^ s * v ^ (-s) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK.le _)

theorem ktSrc_cell_inv_snd (c : ℝ) :
    IntegrableOn (fun x : ℝ × ℝ => (1 + x.2 ^ 2)⁻¹) (B0579.cell c) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ico (-(c / 2)) (c / 2))) :=
    ⟨by simp⟩
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ico (-(c / 2)) (c / 2))) :=
    integrable_const 1
  have h2 : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) (volume.restrict (Set.univ : Set ℝ)) := by
    rw [Measure.restrict_univ]
    exact integrable_inv_one_add_sq
  have h3 := Integrable.mul_prod h1 h2
  have hcell : volume.restrict (B0579.cell c) =
      (volume.restrict (Set.Ico (-(c / 2)) (c / 2))).prod (volume.restrict (Set.univ : Set ℝ)) := by
    rw [B0579.cell, Measure.volume_eq_prod, Measure.prod_restrict]
  unfold IntegrableOn
  rw [hcell]
  simpa using h3

theorem ktSrc_memLp_inv_sqrt (c : ℝ) :
    MemLp (fun x => B0579.jb x ^ (-(1 / 2 : ℝ))) 2 (volume.restrict (B0579.cell c)) := by
  have hm : AEStronglyMeasurable (fun x => B0579.jb x ^ (-(1 / 2 : ℝ)))
      (volume.restrict (B0579.cell c)) :=
    (B0579.continuous_jb_rpow _).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  have e : (fun x => (B0579.jb x ^ (-(1 / 2 : ℝ))) ^ 2) = fun x => (B0579.jb x)⁻¹ := by
    funext x
    rw [← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le, ← Real.rpow_neg_one]
    congr 1
    norm_num
  rw [e]
  refine Integrable.mono' (ktSrc_cell_inv_snd c) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (B0579.continuous_jb.inv₀ fun x => (B0579.jb_pos x).ne').aestronglyMeasurable
  · rw [Real.norm_of_nonneg (inv_nonneg.2 (B0579.jb_pos x).le)]
    refine inv_anti₀ (by positivity) ?_
    unfold B0579.jb
    nlinarith [sq_nonneg x.1]

theorem ktSrc_memLp_pow (c m : ℝ) :
    MemLp (fun x => B0579.jb x ^ (-((m + 1) / 2))) 2 (B0579.cellMeasure c m) := by
  refine (B0579.memLp_cellMeasure_iff c m).2 ?_
  have e : ∀ x : ℝ × ℝ, B0579.bracket x ^ m * B0579.jb x ^ (-((m + 1) / 2))
      = B0579.jb x ^ (-(1 / 2 : ℝ)) := by
    intro x
    rw [B0579.bracket_rpow, B0579.jb_rpow_mul]
    congr 1
    ring
  exact MemLp.ae_eq (ae_of_all _ fun x => (e x).symm) (ktSrc_memLp_inv_sqrt c)

theorem ktSrc_s_le (m : ℝ) (x : ℝ × ℝ) :
    B0579.jb x ^ (-((m + 1) / 2)) ≤ B0579.jb x ^ ((-m) / 2) := by
  rw [show -((m + 1) / 2) = (-m) / 2 + (-(1 / 2 : ℝ)) by ring,
    Real.rpow_add (B0579.jb_pos x)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (B0579.jb_pos x).le _)
    (Real.rpow_le_one_of_one_le_of_nonpos (ktSrc_one_le_jb x) (by norm_num))

theorem ktSource : UnforcedLeray.Short.IIIa.KTSource := by
  intro m hm c hc A
  have hs0 : (0 : ℝ) ≤ (m + 1) / 2 := by linarith
  have hKpos : (0 : ℝ) < 1 + c ^ 2 / 4 := by positivity
  obtain ⟨A1, hA1def⟩ : ∃ A1 : ℝ, A1 = |A| * (1 + c ^ 2 / 4) ^ ((m + 1) / 2) := ⟨_, rfl⟩
  have hA1nn : 0 ≤ A1 := by rw [hA1def]; positivity
  obtain ⟨Fe, hFe⟩ : ∃ Fe : B0579.X c m,
      (⇑Fe =ᵐ[B0579.cellMeasure c m] fun x => B0579.jb x ^ (-((m + 1) / 2))) :=
    ⟨(ktSrc_memLp_pow c m).toLp _, (ktSrc_memLp_pow c m).coeFn_toLp⟩
  refine ⟨A1 * ‖Fe‖ + A1, add_nonneg (mul_nonneg hA1nn (norm_nonneg _)) hA1nn, ?_⟩
  intro B hBc hBA f hf l
  have transfer : ∀ (m' : ℝ) {p : ℝ × ℝ → Prop},
      (∀ᵐ x ∂B0579.cellMeasure c m', p x) → ∀ᵐ x ∂volume.restrict (B0579.cell c), p x :=
    fun m' {p} h => ae_iff.2 ((B0579.ac_cellMeasure c m') (ae_iff.1 h))
  -- pointwise coefficient bound on the cell
  have hBl : ∀ x ∈ B0579.cell c, ‖B l x‖ ≤ A1 * B0579.jb x ^ (-((m + 1) / 2)) := by
    intro x hx
    have hu : 0 < 1 + x.2 ^ 2 := by positivity
    have hpow : (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖B l x‖ ≤ |A| :=
      le_trans (hBA l x) (le_abs_self A)
    have hp : (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) * (1 + x.2 ^ 2) ^ ((m + 1) / 2) = 1 := by
      rw [← Real.rpow_add hu]
      simp
    have hnn : 0 ≤ (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) := Real.rpow_nonneg hu.le _
    have hmul : ‖B l x‖ ≤ |A| * (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) := by
      calc ‖B l x‖ = (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) * ((1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖B l x‖) := by
            rw [← mul_assoc, hp, one_mul]
        _ ≤ (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) * |A| := mul_le_mul_of_nonneg_left hpow hnn
        _ = |A| * (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) := mul_comm _ _
    have hK := ktSrc_rpow_bound hKpos hu (B0579.jb_pos x) (ktSrc_jb_le c x hx) hs0
    calc ‖B l x‖ ≤ |A| * (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) := hmul
      _ ≤ |A| * ((1 + c ^ 2 / 4) ^ ((m + 1) / 2) * B0579.jb x ^ (-((m + 1) / 2))) :=
          mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      _ = A1 * B0579.jb x ^ (-((m + 1) / 2)) := by rw [hA1def]; ring
  have hfm : AEStronglyMeasurable (fun x => f x * (B l x : ℂ)) (volume.restrict (B0579.cell c)) :=
    (hf.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m))).mul
      (Complex.continuous_ofReal.comp (hBc l)).aestronglyMeasurable
  have hpt : ∀ x ∈ B0579.cell c, ‖f x * (B l x : ℂ)‖ ≤
      A1 * (B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) := by
    intro x hx
    rw [norm_mul, Complex.norm_real]
    calc ‖f x‖ * ‖B l x‖ ≤ ‖f x‖ * (A1 * B0579.jb x ^ (-((m + 1) / 2))) :=
          mul_le_mul_of_nonneg_left (hBl x hx) (norm_nonneg _)
      _ = A1 * (B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) := by ring
  have hae1 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖f x * (B l x : ℂ)‖ ≤ A1 * (B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) :=
    (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Filter.Eventually.of_forall fun x hx => hpt x hx)
  have hpt2 : ∀ x ∈ B0579.cell c, ‖f x * (B l x : ℂ)‖ ≤
      A1 * (B0579.jb x ^ ((-m) / 2) * ‖f x‖) := by
    intro x hx
    exact (hpt x hx).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ktSrc_s_le m x) (norm_nonneg _)) hA1nn)
  have hae2 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ‖f x * (B l x : ℂ)‖ ≤ A1 * (B0579.jb x ^ ((-m) / 2) * ‖f x‖) :=
    (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (Filter.Eventually.of_forall fun x hx => hpt2 x hx)
  have hXne : xNorm c (-m) f ≠ ⊤ := hf.eLpNorm_lt_top.ne
  -- the weight and norm of `f`
  have hfa : MemLp (fun x => ‖f x‖) 2 (B0579.cellMeasure c (-m)) := hf.norm
  obtain ⟨aF, haF, haFn⟩ : ∃ aF : B0579.X c (-m),
      (⇑aF =ᵐ[B0579.cellMeasure c (-m)] fun x => ‖f x‖) ∧
        ‖aF‖ = (xNorm c (-m) f).toReal :=
    ⟨hfa.toLp _, hfa.coeFn_toLp, by rw [Lp.norm_toLp, eLpNorm_norm]; rfl⟩
  have hI : IntegrableOn (fun x => B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) (B0579.cell c) := by
    have h0 := B0579.integrableOn_mul_neg c m Fe aF
    refine h0.congr ?_
    filter_upwards [transfer m hFe, transfer (-m) haF] with x h1 h2
    simp only [h1, h2]
  have hnn : 0 ≤ᵐ[volume.restrict (B0579.cell c)]
      (fun x => B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (norm_nonneg _)
  have hIntBound : ∫ x in B0579.cell c, B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖ ≤
      ‖Fe‖ * (xNorm c (-m) f).toReal := by
    have hEq : ∫ x in B0579.cell c, B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖ =
        ∫ x in B0579.cell c, Fe x * aF x := by
      refine integral_congr_ae ?_
      filter_upwards [transfer m hFe, transfer (-m) haF] with x h1 h2
      simp only [h1, h2]
    rw [hEq]
    calc ∫ x in B0579.cell c, Fe x * aF x ≤ |∫ x in B0579.cell c, Fe x * aF x| := le_abs_self _
      _ ≤ ‖Fe‖ * ‖aF‖ := B0579.abs_integral_mul_le c m Fe aF
      _ = ‖Fe‖ * (xNorm c (-m) f).toReal := by rw [haFn]
  have key : eLpNorm (fun x => B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) 1
      (volume.restrict (B0579.cell c)) =
        ENNReal.ofReal (∫ x in B0579.cell c, B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI hnn, eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (norm_nonneg _))]
  -- the `L¹` bound
  have hL1 : eLpNorm (fun x => f x * (B l x : ℂ)) 1 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal (A1 * ‖Fe‖) * xNorm c (-m) f := by
    calc eLpNorm (fun x => f x * (B l x : ℂ)) 1 (volume.restrict (B0579.cell c))
        ≤ eLpNorm (fun x => A1 * (B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖)) 1
            (volume.restrict (B0579.cell c)) := eLpNorm_mono_ae_real hae1
      _ = ‖A1‖ₑ * eLpNorm (fun x => B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) 1
            (volume.restrict (B0579.cell c)) :=
          eLpNorm_const_smul A1 (fun x => B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) 1 _
      _ = ENNReal.ofReal A1 * ENNReal.ofReal
            (∫ x in B0579.cell c, B0579.jb x ^ (-((m + 1) / 2)) * ‖f x‖) := by
          rw [key, Real.enorm_eq_ofReal hA1nn]
      _ ≤ ENNReal.ofReal A1 * ENNReal.ofReal (‖Fe‖ * (xNorm c (-m) f).toReal) :=
          by gcongr
      _ = ENNReal.ofReal (A1 * ‖Fe‖) * xNorm c (-m) f := by
          rw [ENNReal.ofReal_mul (norm_nonneg Fe), ENNReal.ofReal_mul hA1nn,
            ENNReal.ofReal_toReal hXne]
          ring
  -- the `L²` bound
  have hX : eLpNorm (fun x => B0579.jb x ^ ((-m) / 2) * ‖f x‖) 2
      (volume.restrict (B0579.cell c)) = xNorm c (-m) f := by
    have := B0579.eLpNorm_cellMeasure c (-m) (fun x => ‖f x‖)
    rw [eLpNorm_norm] at this
    exact this.symm
  have hL2 : eLpNorm (fun x => f x * (B l x : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal A1 * xNorm c (-m) f := by
    calc eLpNorm (fun x => f x * (B l x : ℂ)) 2 (volume.restrict (B0579.cell c))
        ≤ eLpNorm (fun x => A1 * (B0579.jb x ^ ((-m) / 2) * ‖f x‖)) 2
            (volume.restrict (B0579.cell c)) := eLpNorm_mono_ae_real hae2
      _ = ‖A1‖ₑ * eLpNorm (fun x => B0579.jb x ^ ((-m) / 2) * ‖f x‖) 2
            (volume.restrict (B0579.cell c)) :=
          eLpNorm_const_smul A1 (fun x => B0579.jb x ^ ((-m) / 2) * ‖f x‖) 2 _
      _ = ENNReal.ofReal A1 * xNorm c (-m) f := by
          rw [hX, Real.enorm_eq_ofReal hA1nn]
  have hIB : IntegrableOn (fun x => f x * (B l x : ℂ)) (B0579.cell c) :=
    Integrable.mono' (hI.const_mul A1) hfm hae1
  have hMem : MemLp (fun x => f x * (B l x : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    ⟨hfm, lt_of_le_of_lt hL2
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)⟩
  refine ⟨hIB, hMem, ?_⟩
  calc eLpNorm (fun x => f x * (B l x : ℂ)) 1 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => f x * (B l x : ℂ)) 2 (volume.restrict (B0579.cell c))
      ≤ ENNReal.ofReal (A1 * ‖Fe‖) * xNorm c (-m) f + ENNReal.ofReal A1 * xNorm c (-m) f :=
        add_le_add hL1 hL2
    _ = ENNReal.ofReal (A1 * ‖Fe‖ + A1) * xNorm c (-m) f := by
        rw [ENNReal.ofReal_add (mul_nonneg hA1nn (norm_nonneg _)) hA1nn, add_mul]
