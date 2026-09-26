import MS.Efficiency

open MeasureTheory

set_option linter.style.haveILetI false

namespace MSData

theorem MS_impossible (D : MSData) : False := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability

  let B : ℝ := ∫ t in D.a1..D.b1, D.Q t * D.mu.real {v | t ≤ v}
  let C : ℝ := ∫ t in D.a2..D.b2, D.R t * D.nu.real {c | c ≤ t}

  have hμsupp : ∀ᵐ v ∂D.mu, v ∈ D.mu.support := D.mu.support_mem_ae
  have hνsupp : ∀ᵐ c ∂D.nu, c ∈ D.nu.support := D.nu.support_mem_ae
  have hμprod : ∀ᵐ p ∂(D.mu.prod D.nu), p.1 ∈ D.mu.support := by
    rw [Measure.ae_prod_iff_ae_ae
      (show MeasurableSet {p : ℝ × ℝ | p.1 ∈ D.mu.support} from
        measurableSet_preimage measurable_fst Measure.isClosed_support.measurableSet)]
    filter_upwards [hμsupp] with v hv
    exact Filter.Eventually.of_forall fun _ => hv
  have hνprod : ∀ᵐ p ∂(D.mu.prod D.nu), p.2 ∈ D.nu.support := by
    rw [Measure.ae_prod_iff_ae_ae
      (show MeasurableSet {p : ℝ × ℝ | p.2 ∈ D.nu.support} from
        measurableSet_preimage measurable_snd Measure.isClosed_support.measurableSet)]
    filter_upwards with v
    filter_upwards [hνsupp] with c hc
    exact hc
  have hrect : ∀ᵐ p ∂(D.mu.prod D.nu),
      p.1 ∈ Set.Icc D.a1 D.b1 ∧ p.2 ∈ Set.Icc D.a2 D.b2 := by
    filter_upwards [hμprod, hνprod] with p hpv hpc
    exact ⟨D.mu_supported hpv, D.nu_supported hpc⟩

  have hF1aes : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * D.q p)
      (D.mu.prod D.nu) :=
    measurable_fst.aestronglyMeasurable.mul D.q_measurable
  have hF1 : Integrable (fun p : ℝ × ℝ => p.1 * D.q p) (D.mu.prod D.nu) := by
    apply Integrable.of_bound hF1aes (|D.a1| + |D.b1|)
    filter_upwards [hrect] with p hp
    have hpabs : ‖p.1‖ ≤ |D.a1| + |D.b1| := by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · calc
          -(|D.a1| + |D.b1|) ≤ -|D.a1| := by linarith [abs_nonneg D.b1]
          _ ≤ D.a1 := neg_abs_le _
          _ ≤ p.1 := hp.1.1
      · calc
          p.1 ≤ D.b1 := hp.1.2
          _ ≤ |D.b1| := le_abs_self _
          _ ≤ |D.a1| + |D.b1| := by linarith [abs_nonneg D.a1]
    have hq0 := D.q_nonneg p.1 hp.1 p.2 hp.2
    have hq1 := D.q_le_one p.1 hp.1 p.2 hp.2
    have hqnorm : ‖D.q p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      exact hq1
    calc
      ‖p.1 * D.q p‖ = ‖p.1‖ * ‖D.q p‖ := norm_mul _ _
      _ ≤ (|D.a1| + |D.b1|) * 1 :=
        mul_le_mul hpabs hqnorm (norm_nonneg _) (by positivity)
      _ = |D.a1| + |D.b1| := by ring

  have hF4aes : AEStronglyMeasurable (fun p : ℝ × ℝ => p.2 * D.q p)
      (D.mu.prod D.nu) :=
    measurable_snd.aestronglyMeasurable.mul D.q_measurable
  have hF4 : Integrable (fun p : ℝ × ℝ => p.2 * D.q p) (D.mu.prod D.nu) := by
    apply Integrable.of_bound hF4aes (|D.a2| + |D.b2|)
    filter_upwards [hrect] with p hp
    have hpabs : ‖p.2‖ ≤ |D.a2| + |D.b2| := by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · calc
          -(|D.a2| + |D.b2|) ≤ -|D.a2| := by linarith [abs_nonneg D.b2]
          _ ≤ D.a2 := neg_abs_le _
          _ ≤ p.2 := hp.2.1
      · calc
          p.2 ≤ D.b2 := hp.2.2
          _ ≤ |D.b2| := le_abs_self _
          _ ≤ |D.a2| + |D.b2| := by linarith [abs_nonneg D.a2]
    have hq0 := D.q_nonneg p.1 hp.1 p.2 hp.2
    have hq1 := D.q_le_one p.1 hp.1 p.2 hp.2
    have hqnorm : ‖D.q p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      exact hq1
    calc
      ‖p.2 * D.q p‖ = ‖p.2‖ * ‖D.q p‖ := norm_mul _ _
      _ ≤ (|D.a2| + |D.b2|) * 1 :=
        mul_le_mul hpabs hqnorm (norm_nonneg _) (by positivity)
      _ = |D.a2| + |D.b2| := by ring

  have hbuyerIntegrable :
      Integrable (fun p : ℝ × ℝ => p.1 * D.q p - D.tb p) (D.mu.prod D.nu) :=
    hF1.sub D.tb_integrable
  have hsellerIntegrable :
      Integrable (fun p : ℝ × ℝ => D.tc p - p.2 * D.q p) (D.mu.prod D.nu) :=
    D.tc_integrable.sub hF4

  have he1 : (∫ v, D.U v ∂D.mu) =
      ∫ p, (p.1 * D.q p - D.tb p) ∂(D.mu.prod D.nu) := by
    calc
      (∫ v, D.U v ∂D.mu) =
          ∫ v, (∫ c, v * D.q (v, c) - D.tb (v, c) ∂D.nu) ∂D.mu := by
        apply integral_congr_ae
        filter_upwards with v
        simp [interimU]
      _ = ∫ p, (p.1 * D.q p - D.tb p) ∂(D.mu.prod D.nu) :=
        (integral_prod _ hbuyerIntegrable).symm

  have he2 : (∫ c, D.W c ∂D.nu) =
      ∫ p, (D.tc p - p.2 * D.q p) ∂(D.mu.prod D.nu) := by
    calc
      (∫ c, D.W c ∂D.nu) =
          ∫ c, (∫ v, D.tc (v, c) - c * D.q (v, c) ∂D.mu) ∂D.nu := by
        apply integral_congr_ae
        filter_upwards with c
        simp [interimW]
      _ = ∫ p, (D.tc p - p.2 * D.q p) ∂(D.mu.prod D.nu) :=
        (integral_prod_symm _ hsellerIntegrable).symm

  have htrade : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) * D.q p)
      (D.mu.prod D.nu) := by
    apply (hF1.sub hF4).congr
    filter_upwards with p
    change p.1 * D.q p - p.2 * D.q p = (p.1 - p.2) * D.q p
    ring
  have htransfer : Integrable (fun p : ℝ × ℝ => D.tb p - D.tc p)
      (D.mu.prod D.nu) := D.tb_integrable.sub D.tc_integrable

  have hdecomp :
      (∫ v, D.U v ∂D.mu) + (∫ c, D.W c ∂D.nu) =
        (∫ p, (p.1 - p.2) * D.q p ∂(D.mu.prod D.nu)) -
          ((∫ p, D.tb p ∂(D.mu.prod D.nu)) -
            (∫ p, D.tc p ∂(D.mu.prod D.nu))) := by
    rw [he1, he2]
    calc
      (∫ p, (p.1 * D.q p - D.tb p) ∂(D.mu.prod D.nu)) +
          (∫ p, (D.tc p - p.2 * D.q p) ∂(D.mu.prod D.nu)) =
          ∫ p, ((p.1 * D.q p - D.tb p) + (D.tc p - p.2 * D.q p))
            ∂(D.mu.prod D.nu) := (integral_add hbuyerIntegrable hsellerIntegrable).symm
      _ = ∫ p, ((p.1 - p.2) * D.q p - (D.tb p - D.tc p))
          ∂(D.mu.prod D.nu) := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = (∫ p, (p.1 - p.2) * D.q p ∂(D.mu.prod D.nu)) -
          (∫ p, (D.tb p - D.tc p) ∂(D.mu.prod D.nu)) :=
        integral_sub htrade htransfer
      _ = (∫ p, (p.1 - p.2) * D.q p ∂(D.mu.prod D.nu)) -
          ((∫ p, D.tb p ∂(D.mu.prod D.nu)) -
            (∫ p, D.tc p ∂(D.mu.prod D.nu))) := by
        rw [integral_sub D.tb_integrable D.tc_integrable]

  have haccount :
      (∫ v, D.U v ∂D.mu) + (∫ c, D.W c ∂D.nu) =
        D.S - ((∫ p, D.tb p ∂(D.mu.prod D.nu)) -
          (∫ p, D.tc p ∂(D.mu.prod D.nu))) := by
    rw [hdecomp, D.eff_payoff]
  have hgap : 0 ≤
      (∫ p, D.tb p ∂(D.mu.prod D.nu)) - (∫ p, D.tc p ∂(D.mu.prod D.nu)) :=
    sub_nonneg.mpr D.bb
  have hsum : (∫ v, D.U v ∂D.mu) + (∫ c, D.W c ∂D.nu) ≤ D.S := by
    rw [haccount]
    linarith

  have hEU : (∫ v, D.U v ∂D.mu) = D.U D.a1 + B := by
    simpa [B] using D.EU_eq
  have hEW : (∫ c, D.W c ∂D.nu) = D.W D.b2 + C := by
    simpa [C] using D.EW_eq
  have hBC : B + C > D.S := by
    simpa [B, C] using D.BC_gt_S
  have hsum' : (D.U D.a1 + B) + (D.W D.b2 + C) ≤ D.S := by
    rw [← hEU, ← hEW]
    exact hsum
  have hbase : D.U D.a1 + D.W D.b2 + (B + C) ≤ D.S := by
    nlinarith [hsum']
  have hnegative : D.U D.a1 + D.W D.b2 < 0 := by
    linarith
  have hUa : 0 ≤ D.U D.a1 :=
    D.irB' D.a1 ⟨le_rfl, D.h1.le⟩
  have hWb : 0 ≤ D.W D.b2 :=
    D.irS' D.b2 ⟨D.h2.le, le_rfl⟩
  linarith

end MSData
