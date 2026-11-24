import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.AyContDiff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpBilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpClm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpFderiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpPsij
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpTermBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Bilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54OfS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Snd

/-!
# `PartIII-b:C/asrc/ra/5/4/*` : the `j = 0` term `ψ^p_A` is `C³` with Gaussian bounds

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
Proves `PsipTermReg as χf` (the Prop of `Sub/PartIII-b_C_asrc_ra_5_4.lean`).

With `xj ν 0 x = x`, the term is
`ψ^p_A(s,x) = trace(A^y_mer(s)) * ψ_0(s,x) - ∂_x ψ_0(s,x) (A^y_mer(s) x)`.
* `ψ_0 ∈ GP54 4 ν 3` (`gp54_psij`), `trace ∈ PS54 3` (`ps54_of_s`), product by `gp54_bilin`;
* `∂_x ψ_0 ∈ GP54 4 ν 3` (`gp54_fderiv`), and `x ↦ A^y_mer(s) x` is `PS54 3` (columns of `A^y`
  times the coordinates of `x`), paired with `∂_x ψ_0` by the evaluation bilinear map.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Evaluation pairing `(T, v) ↦ T v` as a continuous bilinear map. -/
def psipReg_ev : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)

theorem psipReg_ev_apply (T : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ × ℝ) : psipReg_ev T v = T v := by
  simp [psipReg_ev, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]

/-- Post-composition with a continuous linear map preserves `PS54`. -/
theorem psipReg_ps54_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (n : ℕ)
    (f : ℝ × (ℝ × ℝ) → E) (hf : PS54 n f) : PS54 n (fun p => L (f p)) := by
  obtain ⟨hC, hB⟩ := hf
  refine ⟨L.contDiff.comp_contDiffOn hC, ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨C, N, hC0, hbd⟩ := hB s0 s1 hs0 hs01
  refine ⟨‖L‖ * C, N, mul_nonneg (norm_nonneg _) hC0, fun m hm s hs x => ?_⟩
  have hp : (s, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨lt_of_lt_of_le hs0 hs.1, trivial⟩
  have hda : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) f (s, x) :=
    hC.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have h1 := L.norm_iteratedFDeriv_comp_left hda (by exact_mod_cast hm)
  calc ‖iteratedFDeriv ℝ m (fun p => L (f p)) (s, x)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f (s, x)‖ := h1
    _ ≤ ‖L‖ * (C * (1 + sq2 x) ^ N) :=
        mul_le_mul_of_nonneg_left (hbd m hm s hs x) (norm_nonneg _)
    _ = ‖L‖ * C * (1 + sq2 x) ^ N := by ring

/-- `PS54` is closed under addition. -/
theorem psipReg_ps54_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (f g : ℝ × (ℝ × ℝ) → E) (hf : PS54 n f) (hg : PS54 n g) :
    PS54 n (fun p => f p + g p) := by
  obtain ⟨hfC, hfB⟩ := hf
  obtain ⟨hgC, hgB⟩ := hg
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  refine ⟨hfC.add hgC, ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨Cf, Nf, hCf, hfb⟩ := hfB s0 s1 hs0 hs01
  obtain ⟨Cg, Ng, hCg, hgb⟩ := hgB s0 s1 hs0 hs01
  refine ⟨Cf + Cg, Nf + Ng, add_nonneg hCf hCg, ?_⟩
  intro m hm s hs x
  have hsU : (0 : ℝ) < s := lt_of_lt_of_le hs0 hs.1
  have hx : (s, x) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hsU, mem_univ x⟩
  have hmN : (m : WithTop ℕ∞) ≤ ((n : ℕ) : WithTop ℕ∞) := by exact_mod_cast hm
  have hfa : ContDiffAt ℝ (m : WithTop ℕ∞) f (s, x) :=
    (hfC.contDiffAt (hU.mem_nhds hx)).of_le hmN
  have hga : ContDiffAt ℝ (m : WithTop ℕ∞) g (s, x) :=
    (hgC.contDiffAt (hU.mem_nhds hx)).of_le hmN
  have hsum : iteratedFDeriv ℝ m (fun p => f p + g p) (s, x)
      = iteratedFDeriv ℝ m f (s, x) + iteratedFDeriv ℝ m g (s, x) :=
    iteratedFDeriv_add_apply hfa hga
  have hsq : (0 : ℝ) ≤ sq2 x := by unfold sq2; positivity
  have hq1 : (1 : ℝ) ≤ 1 + sq2 x := by linarith
  have hP1 : (1 + sq2 x) ^ Nf ≤ (1 + sq2 x) ^ (Nf + Ng) :=
    pow_le_pow_right₀ hq1 (Nat.le_add_right Nf Ng)
  have hP2 : (1 + sq2 x) ^ Ng ≤ (1 + sq2 x) ^ (Nf + Ng) :=
    pow_le_pow_right₀ hq1 (Nat.le_add_left Ng Nf)
  rw [hsum]
  calc ‖iteratedFDeriv ℝ m f (s, x) + iteratedFDeriv ℝ m g (s, x)‖
      ≤ ‖iteratedFDeriv ℝ m f (s, x)‖ + ‖iteratedFDeriv ℝ m g (s, x)‖ := norm_add_le _ _
    _ ≤ Cf * (1 + sq2 x) ^ Nf + Cg * (1 + sq2 x) ^ Ng :=
        add_le_add (hfb m hm s hs x) (hgb m hm s hs x)
    _ ≤ Cf * (1 + sq2 x) ^ (Nf + Ng) + Cg * (1 + sq2 x) ^ (Nf + Ng) :=
        add_le_add (mul_le_mul_of_nonneg_left hP1 hCf) (mul_le_mul_of_nonneg_left hP2 hCg)
    _ = (Cf + Cg) * (1 + sq2 x) ^ (Nf + Ng) := by ring

theorem psipTermReg (as : ℝ) (χf : ℝ → ℝ) : PsipTermReg as χf := by
  unfold PsipTermReg
  intro hχ ν hν A hA
  have hAy : ContDiffOn ℝ ((6 : ℕ) : WithTop ℕ∞) (Ay ν χf A) (Ioi (0 : ℝ)) :=
    ay54_contDiffOn as χf hχ ν A hA
  have hA3 : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (Ay ν χf A) (Ioi (0 : ℝ)) :=
    hAy.of_le (by exact_mod_cast (by norm_num : (3 : ℕ) ≤ 6))
  have hent : ∀ i j : Fin 3, ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun s => Ay ν χf A s i j) (Ioi (0 : ℝ)) := by
    intro i j
    have hE : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun M : Mat3 => M i j) :=
      contDiff_apply_apply ℝ ℝ i j
    exact hE.comp_contDiffOn hA3
  -- the trace of the meridional block, a function of `s` alone
  have hTrS : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun s => merTrace (Ay ν χf A s)) (Ioi (0 : ℝ)) :=
    (hent 0 0).add (hent 2 2)
  have hTr : PS54 3 (fun p : ℝ × (ℝ × ℝ) => merTrace (Ay ν χf A p.1)) :=
    ps54_of_s 3 (fun s => merTrace (Ay ν χf A s)) hTrS
  -- the Gaussian `ψ_0` and its first fibre derivative
  have hPsi : GP54 4 ν 3 (fun p : ℝ × (ℝ × ℝ) => psij ν p.1 0 p.2) :=
    gp54_psij ν hν 3
  have hT1 : GP54 4 ν 3 (fun p : ℝ × (ℝ × ℝ) =>
      ContinuousLinearMap.mul ℝ ℝ (psij ν p.1 0 p.2) (merTrace (Ay ν χf A p.1))) :=
    gp54_bilin (ContinuousLinearMap.mul ℝ ℝ) 4 ν 3
      (fun p : ℝ × (ℝ × ℝ) => psij ν p.1 0 p.2)
      (fun p : ℝ × (ℝ × ℝ) => merTrace (Ay ν χf A p.1)) hPsi hTr
  have hD : GP54 4 ν 3 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (psij ν p.1 0) p.2) :=
    gp54_fderiv 4 ν 3 (fun p : ℝ × (ℝ × ℝ) => psij ν p.1 0 p.2) (gp54_psij ν hν 4)
  -- the meridional block applied to `x`, as a combination of the columns of `A^y`
  have hc1 : PS54 3 (fun p : ℝ × (ℝ × ℝ) => (Ay ν χf A p.1 0 0, Ay ν χf A p.1 2 0)) :=
    ps54_of_s 3 (fun s => (Ay ν χf A s 0 0, Ay ν χf A s 2 0))
      ((hent 0 0).prodMk (hent 2 0))
  have hc2 : PS54 3 (fun p : ℝ × (ℝ × ℝ) => (Ay ν χf A p.1 0 2, Ay ν χf A p.1 2 2)) :=
    ps54_of_s 3 (fun s => (Ay ν χf A s 0 2, Ay ν χf A s 2 2))
      ((hent 0 2).prodMk (hent 2 2))
  have hx1 : PS54 3 (fun p : ℝ × (ℝ × ℝ) => p.2.1) :=
    psipReg_ps54_clm (ContinuousLinearMap.fst ℝ ℝ ℝ) 3 (fun p : ℝ × (ℝ × ℝ) => p.2)
      (ps54_snd 3)
  have hx2 : PS54 3 (fun p : ℝ × (ℝ × ℝ) => p.2.2) :=
    psipReg_ps54_clm (ContinuousLinearMap.snd ℝ ℝ ℝ) 3 (fun p : ℝ × (ℝ × ℝ) => p.2)
      (ps54_snd 3)
  have hm1 : PS54 3 (fun p : ℝ × (ℝ × ℝ) =>
      p.2.1 • (Ay ν χf A p.1 0 0, Ay ν χf A p.1 2 0)) :=
    ps54_bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) 3
      (fun p : ℝ × (ℝ × ℝ) => p.2.1)
      (fun p : ℝ × (ℝ × ℝ) => (Ay ν χf A p.1 0 0, Ay ν χf A p.1 2 0)) hx1 hc1
  have hm2 : PS54 3 (fun p : ℝ × (ℝ × ℝ) =>
      p.2.2 • (Ay ν χf A p.1 0 2, Ay ν χf A p.1 2 2)) :=
    ps54_bilin (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) 3
      (fun p : ℝ × (ℝ × ℝ) => p.2.2)
      (fun p : ℝ × (ℝ × ℝ) => (Ay ν χf A p.1 0 2, Ay ν χf A p.1 2 2)) hx2 hc2
  have hv : PS54 3 (fun p : ℝ × (ℝ × ℝ) => merApply (Ay ν χf A p.1) p.2) := by
    have e : (fun p : ℝ × (ℝ × ℝ) => merApply (Ay ν χf A p.1) p.2) =
        (fun p : ℝ × (ℝ × ℝ) =>
          p.2.1 • (Ay ν χf A p.1 0 0, Ay ν χf A p.1 2 0)
            + p.2.2 • (Ay ν χf A p.1 0 2, Ay ν χf A p.1 2 2)) := by
      funext p
      ext <;> simp [merApply] <;> ring
    rw [e]
    exact psipReg_ps54_add 3 _ _ hm1 hm2
  -- the fibre derivative paired with the block applied to `x`
  have hT2 : GP54 4 ν 3 (fun p : ℝ × (ℝ × ℝ) =>
      psipReg_ev (fderiv ℝ (psij ν p.1 0) p.2) (merApply (Ay ν χf A p.1) p.2)) :=
    gp54_bilin psipReg_ev 4 ν 3 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (psij ν p.1 0) p.2)
      (fun p : ℝ × (ℝ × ℝ) => merApply (Ay ν χf A p.1) p.2) hD hv
  have hneg : GP54 4 ν 3 (fun p : ℝ × (ℝ × ℝ) =>
      (-(ContinuousLinearMap.id ℝ ℝ) : ℝ →L[ℝ] ℝ)
        (psipReg_ev (fderiv ℝ (psij ν p.1 0) p.2) (merApply (Ay ν χf A p.1) p.2))) :=
    gp54_clm (-(ContinuousLinearMap.id ℝ ℝ) : ℝ →L[ℝ] ℝ) 4 ν 3
      (fun p : ℝ × (ℝ × ℝ) =>
        psipReg_ev (fderiv ℝ (psij ν p.1 0) p.2) (merApply (Ay ν χf A p.1) p.2)) hT2
  have hfin := gp54_add 4 ν 3
    (fun p : ℝ × (ℝ × ℝ) =>
      ContinuousLinearMap.mul ℝ ℝ (psij ν p.1 0 p.2) (merTrace (Ay ν χf A p.1)))
    (fun p : ℝ × (ℝ × ℝ) =>
      (-(ContinuousLinearMap.id ℝ ℝ) : ℝ →L[ℝ] ℝ)
        (psipReg_ev (fderiv ℝ (psij ν p.1 0) p.2) (merApply (Ay ν χf A p.1) p.2)))
    hT1 hneg
  have hG : GP54 4 ν 3 (fun p : ℝ × (ℝ × ℝ) => psipATerm ν χf A p.1 p.2 0) := by
    have e : (fun p : ℝ × (ℝ × ℝ) => psipATerm ν χf A p.1 p.2 0) =
        (fun p : ℝ × (ℝ × ℝ) =>
          ContinuousLinearMap.mul ℝ ℝ (psij ν p.1 0 p.2) (merTrace (Ay ν χf A p.1))
            + (-(ContinuousLinearMap.id ℝ ℝ) : ℝ →L[ℝ] ℝ)
                (psipReg_ev (fderiv ℝ (psij ν p.1 0) p.2) (merApply (Ay ν χf A p.1) p.2))) := by
      funext p
      simp only [psipATerm, xj_zero, psipReg_ev_apply, ContinuousLinearMap.mul_apply',
        neg_apply, ContinuousLinearMap.id_apply]
      ring
    rw [e]
    exact hfin
  exact ⟨hG.1, gp54_termBound 4 ν (by norm_num) hν 3 _ hG⟩

end UnforcedLeray.Short.PartIIIb.Concrete
