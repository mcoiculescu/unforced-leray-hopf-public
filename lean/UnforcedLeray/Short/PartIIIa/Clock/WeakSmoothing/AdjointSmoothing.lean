import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Of
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.CommuteOf
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTSource
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTPairInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakMeas
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakCong
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakAdd
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTCoeffDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTTestInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakLeibniz
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakIBP
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelIsBS
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.MollRateDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.StaticMollEnergy
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainGradBdd
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollWeakDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellWeakDerivOfMollBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellInterp
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CompactJetBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TestedDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetPartialBdd
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.JetNormOfPartials
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.ExtCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.ExtDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.AgeAeCell
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.WeightedH1
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.WeightedH1Cont
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont

/-!
# `PartIII-a:T21/2/7/2`: `AdjointWeakRegular` for `8 < m`

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073.
Assembly of `adjointWeakRegular_of` (`Sub/PartIIIa_T21_2_7_2.lean`) from the four leaves:
- `AdjointWeakSmoothVersion` (`PartIII-a:T21/2/7/2/1`),
- `adjointWeakH1` (`PartIII-a:T21/2/7/2/2`),
- `adjointWeakH1Cont` (`PartIII-a:T21/2/7/2/3`),
- `adjointWeakHigherCont` (`PartIII-a:T21/2/7/2/4`).

Note: `SmoothVersion.lean` transitively imports `Sub/AdjInterior/HkStep/KT/BaseOf.lean`, which
declares `UnforcedLeray.Short.IIIa.xNorm_le_h1Norm`, colliding with the declaration of the same
name in `Sub/PartIII-a_T21_2_3_1_8_1.lean` (transitively imported by `WeightedH1`,
`WeightedH1Cont`, and `HigherCont`). We inline the one-line assemblies of `SmoothVersion` and
`ktOrderMinusOneUnif_of` with private helpers to avoid importing `BaseOf.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

private theorem xNorm_le_h1Norm_both (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    xNorm c (-m) φ ≤ h1Norm c m φ g ∧ ∀ j, xNorm c (-m) (g j) ≤ h1Norm c m φ g := by
  have key : ∀ a : ℝ≥0∞, a ^ 2 ≤ xNorm c (-m) φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2 →
      a ≤ h1Norm c m φ g := by
    intro a ha
    unfold h1Norm
    calc a = (a ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow ha (by norm_num)
  refine ⟨key _ le_self_add, fun j => key _ ?_⟩
  refine le_trans ?_ le_add_self
  exact Finset.single_le_sum (f := fun j => xNorm c (-m) (g j) ^ 2) (fun _ _ => zero_le)
    (Finset.mem_univ j)

private def ktJet1' (χ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) : List (Fin 2) → ℝ × ℝ → ℂ
  | [] => χ
  | [k] => g k
  | _ :: _ :: _ => 0

private def KTAtU' (m c : ℝ) (j : ℕ) : Prop :=
  ∀ (A : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Fin 2 → ℝ × ℝ → ℝ),
    (∀ l, ContDiff ℝ ∞ (B l)) → (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    KTCoeffBound m j B A →
    ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m j f D →
      ∃ (χ : ℝ × ℝ → ℂ) (Dχ : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m (j + 1) χ Dχ ∧
        (∀ w : List (Fin 2), w.length ≤ j + 1 →
          xNorm c (-m) (Dχ w) ≤ ENNReal.ofReal C * jetNorm c m j D) ∧
        KTPairing c f B χ

private def KTBaseU' (m : ℝ) : Prop := 1 < m → ∀ c : ℝ, 1 ≤ c → KTAtU' m c 0

private theorem ktAtU_succ' {m c : ℝ} (hm : 1 < m) (hc : 1 ≤ c) (hBase : KTBaseU' m)
    (hComm : KTCommute m) (hCD : KTCoeffDeriv) (hAdd : KTWeakAdd) (j : ℕ) (ih : KTAtU' m c j) :
    KTAtU' m c (j + 1) := by
  intro A
  obtain ⟨C0, hC0, H0⟩ := hBase hm c hc A
  obtain ⟨C1, hC1, H1⟩ := ih A
  refine ⟨C0 + C1 + C1 + C1, by linarith, ?_⟩
  intro B hBs hBp hBb
  have hb1 : KTCoeffBound m 1 B A := fun l i hi x => hBb l i (by omega) x
  have hb0 : KTCoeffBound m 0 B A := fun l i hi x => hBb l i (by omega) x
  have hbj : KTCoeffBound m j B A := fun l i hi x => hBb l i (hi.trans (Nat.le_succ _)) x
  have hder := fun k : Fin 2 => hCD m c j B A k hBs hBp hBb
  have H2 := fun k : Fin 2 => H1 (fun l => B0579.pd k (B l)) (hder k).1 (hder k).2.1 (hder k).2.2
  have H0 := H0 B hBs hBp hb0
  have H1 := H1 B hBs hBp hbj
  intro f D hJ
  obtain ⟨χ, Dχ, hχJ, hχN, hχP⟩ := H0 f D (hJ.mono (Nat.zero_le _))
  have hex : ∀ k : Fin 2, ∃ (χ₁ χ₂ : ℝ × ℝ → ℂ) (E₁ E₂ : List (Fin 2) → ℝ × ℝ → ℂ),
      IsCellJet c m (j + 1) χ₁ E₁ ∧ IsCellJet c m (j + 1) χ₂ E₂ ∧
      (∀ w : List (Fin 2), w.length ≤ j + 1 →
        xNorm c (-m) (E₁ w) ≤ ENNReal.ofReal C1 * jetNorm c m j (fun w => D (w ++ [k]))) ∧
      (∀ w : List (Fin 2), w.length ≤ j + 1 →
        xNorm c (-m) (E₂ w) ≤ ENNReal.ofReal C1 * jetNorm c m j D) ∧
      KTPairing c (D [k]) B χ₁ ∧ KTPairing c f (fun l => B0579.pd k (B l)) χ₂ := by
    intro k
    obtain ⟨χ₁, E₁, a1, a2, a3⟩ := H1 (D [k]) (fun w => D (w ++ [k])) (hJ.shift k)
    obtain ⟨χ₂, E₂, b1, b2, b3⟩ := H2 k f D (hJ.mono (Nat.le_succ _))
    exact ⟨χ₁, χ₂, E₁, E₂, a1, b1, a2, b2, a3, b3⟩
  choose χ₁ χ₂ E₁ E₂ hE₁ hE₂ hN₁ hN₂ hP₁ hP₂ using hex
  have hcomm : ∀ k : Fin 2, HasWeakCellDerivC c k χ (χ₁ k + χ₂ k) := by
    intro k
    have hχ0 : MemLp χ 2 (B0579.cellMeasure c (-m)) := by
      have := hχJ.memX [] (Nat.zero_le _)
      rwa [hχJ.base] at this
    have hf0 : MemLp f 2 (B0579.cellMeasure c (-m)) := by
      have := hJ.memX [] (Nat.zero_le _)
      rwa [hJ.base] at this
    exact hComm hm c hc B A k hBs hBp hb1 f (D [k]) χ (χ₁ k) (χ₂ k) hf0
      (by simpa using hJ.memX [k] (by simp)) hχ0
      (by simpa [(hE₁ k).base] using (hE₁ k).memX [] (Nat.zero_le _))
      (by simpa [(hE₂ k).base] using (hE₂ k).memX [] (Nat.zero_le _))
      (by simpa [hJ.base] using hJ.deriv k [] (Nat.succ_pos _)) hχP (hP₁ k) (hP₂ k)
  refine ⟨χ, ktGlue χ (fun k => E₁ k + E₂ k), ?_, ?_, hχP⟩
  · have hJk : ∀ k : Fin 2, IsCellJet c m (j + 1) (χ₁ k + χ₂ k) (E₁ k + E₂ k) :=
      fun k => (hE₁ k).add hAdd (hE₂ k)
    have hbase : ∀ k : Fin 2, (E₁ k + E₂ k) [] = χ₁ k + χ₂ k := fun k => (hJk k).base
    have hχ0 : ktGlue χ (fun k => E₁ k + E₂ k) [] = χ := rfl
    refine ⟨hχ0, ?_, ?_, ?_⟩
    · intro w hw x
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hχJ.periodic [] (Nat.zero_le _) x
        rwa [hχJ.base] at this
      · rw [ktGlue_append]
        exact (hJk k).periodic L (by simpa using hw) x
    · intro w hw
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hχJ.memX [] (Nat.zero_le _)
        rwa [hχJ.base] at this
      · rw [ktGlue_append]
        exact (hJk k).memX L (by simpa using hw)
    · intro i w hw
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hcomm i
        rw [show [i] = [] ++ [i] from rfl, ktGlue_append, ktGlue_nil]
        simpa [← hbase i] using this
      · rw [show i :: (L ++ [k]) = (i :: L) ++ [k] from rfl, ktGlue_append, ktGlue_append]
        exact (hJk k).deriv i L (by simpa using hw)
  · intro w hw
    rcases ktSplit w with rfl | ⟨w', k, rfl⟩
    · calc xNorm c (-m) (ktGlue χ (fun k => E₁ k + E₂ k) []) = xNorm c (-m) χ := rfl
        _ ≤ ENNReal.ofReal C0 * jetNorm c m 0 D := by
          have := hχN [] (Nat.zero_le _)
          rwa [hχJ.base] at this
        _ ≤ ENNReal.ofReal (C0 + C1 + C1 + C1) * jetNorm c m (j + 1) D := by
          refine mul_le_mul' ?_ (jetNorm_mono c m (Nat.zero_le _) D)
          exact ENNReal.ofReal_le_ofReal (by linarith [hC1, hC1])
    · rw [ktGlue_append]
      have hw' : w'.length ≤ j + 1 := by simpa using hw
      have e : xNorm c (-m) ((E₁ k + E₂ k) w') ≤
          xNorm c (-m) (E₁ k w') + xNorm c (-m) (E₂ k w') := by
        unfold xNorm
        exact eLpNorm_add_le ((hE₁ k).memX w' hw').aestronglyMeasurable
          ((hE₂ k).memX w' hw').aestronglyMeasurable (by norm_num)
      have j1 : jetNorm c m j (fun w => D (w ++ [k])) ≤ jetNorm c m (j + 1) D :=
        jetNorm_shift_le c m j k D
      have j2 : jetNorm c m j D ≤ jetNorm c m (j + 1) D := jetNorm_mono c m (Nat.le_succ _) D
      have hsum : ENNReal.ofReal C1 + ENNReal.ofReal C1 ≤
          ENNReal.ofReal (C0 + C1 + C1 + C1) := by
        rw [← ENNReal.ofReal_add hC1 hC1]
        exact ENNReal.ofReal_le_ofReal (by linarith [hC0, hC1])
      calc xNorm c (-m) ((E₁ k + E₂ k) w')
          ≤ xNorm c (-m) (E₁ k w') + xNorm c (-m) (E₂ k w') := e
        _ ≤ ENNReal.ofReal C1 * jetNorm c m j (fun w => D (w ++ [k])) +
            ENNReal.ofReal C1 * jetNorm c m j D :=
          add_le_add (hN₁ k w' hw') (hN₂ k w' hw')
        _ ≤ ENNReal.ofReal C1 * jetNorm c m (j + 1) D +
            ENNReal.ofReal C1 * jetNorm c m (j + 1) D :=
          add_le_add (mul_le_mul' le_rfl j1) (mul_le_mul' le_rfl j2)
        _ = (ENNReal.ofReal C1 + ENNReal.ofReal C1) * jetNorm c m (j + 1) D := by
          rw [add_mul]
        _ ≤ _ := mul_le_mul' hsum le_rfl

private theorem ktBaseU_of' (m : ℝ) (hK : KernelAdjointBound m) (hS : KTSource) (hP : KTPairInt)
    (hM : KTWeakMeas) (hCong : KTWeakCong) : KTBaseU' m := by
  intro hm c hc A
  have hc0 : 0 < c := by linarith
  obtain ⟨CS, hCS, HS0⟩ := hS m hm c hc0 A
  obtain ⟨CK, hCK, HK⟩ := hK hm
  refine ⟨2 * CK * CS, by positivity, ?_⟩
  intro B hBs hBp hb
  have HS := HS0 B (fun l => (hBs l).continuous) (by
    intro l x
    have := hb l 0 le_rfl x
    simpa using this)
  intro f D hJ
  have hf0 : MemLp f 2 (B0579.cellMeasure c (-m)) := by
    have := hJ.memX [] (Nat.zero_le _)
    rwa [hJ.base] at this
  have hjet : jetNorm c m 0 D = xNorm c (-m) f := by
    simp [jetNorm, wordsLE, hJ.base]
  set F : Fin 2 → ℝ × ℝ → ℂ := fun l x => f x * (B l x : ℂ) with hF
  have hFs := fun l => HS f hf0 l
  obtain ⟨χ0, gχ, hweak, hnorm, hpair⟩ :=
    HK c hc F (fun l => ⟨(hFs l).1, (hFs l).2.1⟩)
  obtain ⟨hmeas0, hmeasg⟩ := hM c χ0 gχ hc0 hweak
  have hsumle : ∑ j, (eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
      eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) ≤
        2 * (ENNReal.ofReal CS * xNorm c (-m) f) := by
    rw [Fin.sum_univ_two, two_mul]
    exact add_le_add (hFs 0).2.2 (hFs 1).2.2
  have hH : h1Norm c m χ0 gχ ≤ ENNReal.ofReal (2 * CK * CS) * xNorm c (-m) f := by
    calc h1Norm c m χ0 gχ ≤ ENNReal.ofReal CK * ∑ j, (eLpNorm (F j) 1
          (volume.restrict (B0579.cell c)) + eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) :=
          hnorm
      _ ≤ ENNReal.ofReal CK * (2 * (ENNReal.ofReal CS * xNorm c (-m) f)) :=
          mul_le_mul' le_rfl hsumle
      _ = ENNReal.ofReal (2 * CK * CS) * xNorm c (-m) f := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp only [ENNReal.ofReal_ofNat]
          ring
  have hxf : xNorm c (-m) f ≠ ⊤ := hf0.eLpNorm_ne_top
  have hHtop : h1Norm c m χ0 gχ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hxf) hH
  obtain ⟨hxχ, hxg⟩ := xNorm_le_h1Norm_both c m χ0 gχ
  have hmem : ∀ φ : ℝ × ℝ → ℂ, AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) →
      xNorm c (-m) φ ≠ ⊤ → MemLp (perRep c φ) 2 (B0579.cellMeasure c (-m)) := by
    intro φ hφ hne
    have hae := perRep_ae_cellMeasure hc0 (-m) φ
    refine ⟨?_, ?_⟩
    · exact ((hφ.mono_ac (B0579.cellMeasure_ac c (-m))).congr hae.symm)
    · rw [eLpNorm_congr_ae hae]
      exact lt_top_iff_ne_top.2 hne
  have hpt : ∀ x : ℝ × ℝ, ∀ u : Fin 2 → ℝ,
      f x * ((u 0 * B 0 x + u 1 * B 1 x : ℝ) : ℂ) = F 0 x * (u 0 : ℂ) + F 1 x * (u 1 : ℂ) := by
    intro x u
    simp only [hF]
    push_cast
    ring
  have hnX : ∀ φ : ℝ × ℝ → ℂ, xNorm c (-m) (perRep c φ) = xNorm c (-m) φ := fun φ =>
    eLpNorm_congr_ae (perRep_ae_cellMeasure hc0 (-m) φ)
  have hbd : xNorm c (-m) χ0 ≤ ENNReal.ofReal (2 * CK * CS) * jetNorm c m 0 D ∧
      ∀ j, xNorm c (-m) (gχ j) ≤ ENNReal.ofReal (2 * CK * CS) * jetNorm c m 0 D := by
    rw [hjet]
    exact ⟨hxχ.trans hH, fun j => (hxg j).trans hH⟩
  have hper : ∀ φ : ℝ × ℝ → ℂ, ∀ x : ℝ × ℝ, perRep c φ (x.1 + c, x.2) = perRep c φ x :=
    fun φ x => perRep_periodic hc0 φ x
  refine ⟨perRep c χ0, ktJet1' (perRep c χ0) (fun k => perRep c (gχ k)), ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro w hw x
      match w, hw with
      | [], _ => exact hper _ x
      | [k], _ => exact hper (gχ k) x
      | _ :: _ :: _, hw => simp at hw
    · intro w hw
      match w, hw with
      | [], _ => exact hmem χ0 hmeas0 (ne_top_of_le_ne_top hHtop hxχ)
      | [k], _ => exact hmem (gχ k) (hmeasg k) (ne_top_of_le_ne_top hHtop (hxg k))
      | _ :: _ :: _, hw => simp at hw
    · intro j w hw
      match w, hw with
      | [], _ =>
        exact hCong c j χ0 (gχ j) _ _ (hweak j) (perRep_ae_cell hc0 χ0)
          (perRep_ae_cell hc0 (gχ j))
      | _ :: _, hw => simp at hw
  · intro w hw
    match w, hw with
    | [], _ => show xNorm c (-m) (perRep c χ0) ≤ _
               rw [hnX]; exact hbd.1
    | [k], _ => show xNorm c (-m) (perRep c (gχ k)) ≤ _
                rw [hnX]; exact hbd.2 k
    | _ :: _ :: _, hw => simp at hw
  · intro ψ uψ hψ hu
    have hi := hP c F (fun l => ⟨(hFs l).1, (hFs l).2.1⟩) ψ uψ hψ hu
    have hpr := hpair ψ uψ hψ hu
    have hfun : (fun x => f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ)) =
        fun x => F 0 x * (uψ x 0 : ℂ) + F 1 x * (uψ x 1 : ℂ) := funext fun x => hpt x _
    refine ⟨by rw [hfun]; exact hi, ?_⟩
    rw [hfun]
    calc ∫ x in B0579.cell c, perRep c χ0 x * (ψ x : ℂ)
        = ∫ x in B0579.cell c, χ0 x * (ψ x : ℂ) := by
          refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x hx => ?_
          rw [perRep_of_mem_cell hc0 χ0 hx]
      _ = ∫ x in B0579.cell c, ∑ j, F j x * ((uψ x j : ℝ) : ℂ) := hpr
      _ = _ := by simp [Fin.sum_univ_two]

private theorem ktOrderMinusOneUnif_of_parts' (m : ℝ) (hBase : KTBaseU' m) (hComm : KTCommute m)
    (hCD : KTCoeffDeriv) (hAdd : KTWeakAdd) : KTOrderMinusOneUnif m := by
  intro hm c hc j A
  have : ∀ j, KTAtU' m c j := by
    intro j
    induction j with
    | zero => exact hBase hm c hc
    | succ j ih => exact ktAtU_succ' hm hc hBase hComm hCD hAdd j ih
  obtain ⟨C, hC0, H⟩ := this j A
  exact ⟨C, hC0, fun B hB hBp hBb f D hJ => H B hB hBp hBb f D hJ⟩

private theorem ktOrderMinusOneUnif' (m : ℝ) : KTOrderMinusOneUnif m :=
  ktOrderMinusOneUnif_of_parts' m
    (ktBaseU_of' m (kernelAdjointBound m) _root_.ktSource ktPairInt ktWeakMeas _root_.ktWeakCong)
    (ktCommute_of m _root_.ktSource _root_.ktCoeffDeriv _root_.ktWeakLeibniz ktWeakIBP
      kerVelSmooth kerVelIsBS _root_.ktTestInt)
    _root_.ktCoeffDeriv _root_.ktWeakAdd

private theorem adjMollEnergy' (m : ℝ) (hm : 8 < m) : AdjMollEnergy m :=
  adjMollEnergy_of m hm (mollRateDeriv m hm) (staticMollEnergy m) trainSliceVel trainGradBdd
    (ktOrderMinusOneUnif' m)

private theorem adjHkStep' (m : ℝ) (hm : 8 < m) : AdjHkStep m :=
  adjHkStep_of m (adjHkGainOn_of m (adjMollEnergy' m hm) cellMollSmooth cellMollBound
    cellMollWeakDeriv cellWeakDerivOfMollBound) cellInterp weakCellAeUnique compactJetBound

private theorem adjointInteriorSmooth' (m : ℝ) (hm : 8 < m) : AdjointInteriorSmooth m :=
  adjointInteriorSmooth_of m (adjointInteriorSmoothBUC_of m (trainSTJetsOfBUC m hm)
    (adjointInteriorSmoothJets_of m (adjTestedDerivOf m) (adjHkStep' m hm) (adjTimeJetsOf m hm)
      timeJetsSTSobolev stSobolevSmoothRep stRepSliceAe))

private theorem adjHkStepEnd' (m : ℝ) (hm : 8 < m) : AdjHkStepEnd m :=
  adjHkStepEnd_of m
    (adjHkGainOn_of m (adjMollEnergy' m hm) cellMollSmooth cellMollBound cellMollWeakDeriv
      cellWeakDerivOfMollBound)
    cellInterp weakCellAeUnique compactJetBound

private theorem adjointEndpointSmooth' (m : ℝ) (hm : 8 < m) : AdjointEndpointSmooth m :=
  adjointEndpointSmooth_of m
    (adjEndJets_of m (adjEndJetsBUC_of m (trainSTJetsOfBUC m hm) (adjTestedDerivOf m)
      (adjHkStepEnd' m hm) (adjTimeJetsEnd m hm)
      (endJetBddOfTimeJets_of timeJetPartialBdd jetNormOfPartials)))
    endExtCont endExtDeriv endAgeAeCell

private theorem adjointWeakSmoothVersion' (m : ℝ) (hm : 8 < m) : AdjointWeakSmoothVersion m :=
  adjointWeakSmoothVersion_of m (adjointInteriorSmooth' m hm) (adjointEndpointSmooth' m hm)

theorem adjointSmoothing (m : ℝ) (hm : 8 < m) : AdjointWeakRegular m :=
  adjointWeakRegular_of m (adjointWeakSmoothVersion' m hm) (adjointWeakH1 m hm)
    (adjointWeakH1Cont m hm) (adjointWeakHigherCont m hm)

end UnforcedLeray.Short.IIIa
