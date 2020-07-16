####################################################
# Supporting R script for: Metelmann et al. 2020,  #
# PAPER TITLE GOES HERE                            #
#                                                  #
# Compiled by S. Metelmann, K. Pattni, L. Brierley #
#          University of Liverpool, 2020           #
####################################################

#################
# Library setup #
#################

rm(list = ls())

# Read in required packages
library(car)
library(effects)
library(ggplot2)
library(ggeffects)
library(lme4)
library(lmerTest)
library(MASS)
library(missForest)
library(ggpubr)
library(MuMIn)
library(relaimpo)
library(corrplot)
library(tidyverse) # Load the tidyverse package for many helper functions for data frames

# Load relative importance package, but install non-US version of package containing pmvd function not in CRAN version if not installed
# Note that this package is NOT licensed for use in the USA, see: https://prof.beuth-hochschule.de/groemping/software/relaimpo/
if (!require(relaimpo)) {
  install.packages("https://prof.beuth-hochschule.de/fileadmin/prof/groemp/downloads/relaimpo_2.2-3.tar.gz", method = "libcurl", repos = NULL)
  library(relaimpo)
}

###############
# Set options #
###############

# Select analysis, 1: all cities; 2: all cities without China; 3: China only
analysis <- 2
# Select named outcome column to use
outcome <- "R0"

###############################
# Define additional functions #
###############################

# VIF for mixed-effects regression, source: https://github.com/aufrank/R-hacks/blob/master/mer-utils.R
vif.mer <- function(fit) {
  v <- vcov(fit)
  nam <- names(fixef(fit))

  ns <- sum(1 * (nam == "Intercept" | nam == "(Intercept)"))
  if (ns > 0) {
    v <- v[-(1:ns), -(1:ns), drop = FALSE]
    nam <- nam[-(1:ns)]
  }

  d <- diag(v)^0.5
  v <- diag(solve(v / (d %o% d)))
  names(v) <- nam
  v
}

# Correlation across covariates
cor_mtest <- function(mat, method) {
  mat <- as.matrix(mat)
  n <- ncol(mat)
  p.mat <- matrix(NA, n, n)
  diag(p.mat) <- 0
  for (i in 1:(n - 1)) {
    for (j in (i + 1):n) {
      tmp <- cor.test(mat[, i], mat[, j], method = method)
      p.mat[i, j] <- p.mat[j, i] <- tmp$p.value
    }
  }
  colnames(p.mat) <- rownames(p.mat) <- colnames(mat)
  p.mat
}

# Relative importance for mixed-effects regression, adapted from source: https://gist.github.com/BERENZ/e9b581a4b7160357934e
calc.relimp.mm <- function(model, rela, type = "lmg") {
  if (class(model) == "lm") {
    importances <- calc.relimp(model, rela = rela, type = type)
    return(importances)
  } else if (class(model) == "lmerModLmerTest") {
    require(lme4)
    X <- getME(model, "X")
    X <- X[, -1]
    Y <- getME(model, "y")
    s_resid <- sigma(model)
    s_effect <- getME(model, "theta") * s_resid
    s2 <- sum(s_resid^2, s_effect^2)
    V <- Diagonal(x = s2, n = nrow(X))
    YX <- cbind(Y, X)
    cov_XY <- solve(t(YX) %*% solve(V) %*% as.matrix(YX))
    colnames(cov_XY) <- rownames(cov_XY) <- colnames(YX)
    importances <- calc.relimp(as.matrix(cov_XY), rela = rela, type = type)
    return(importances)
  } else {
    stop("model class not recognised", call. = FALSE)
  }
}

#########################
# Read and process data #
#########################

# Read in data, selecting relevant rows
all <- read.csv("Metelmann_et_al_covariates.csv", header = T, sep = ",", stringsAsFactors = FALSE, na.strings = c("NA"))

if (analysis == 1) {
  suffix <- "_all"
} else if (analysis == 2) {
  suffix <- "_without_china"
  all <- subset(all, Country != "China")
} else if (analysis == 3) {
  suffix <- "_china"
  all <- subset(all, Country == "China")
}

# Prepare data for modelling
all <- all %>%
  mutate(
    GDP_city = coalesce(as.numeric(GDP_city), GDP_country), # Substitute in country average GDP if no city-level data
    Elder_city = coalesce(Elder_city, Elder_country), # Substitute in country average elder dependency ratio if no city-level data
    Airqual_city = coalesce(Airqual_city, Airqual_country), # Substitute in country average air pollution exposure if no city-level data
    DayS = as.numeric(as.Date(as.character(all$DayS), format = "%m/%d/%Y") - as.Date("2020-01-01")), # Convert DayS to calendar days
    DayE = as.numeric(as.Date(as.character(all$DayE), format = "%m/%d/%Y") - as.Date("2020-01-01")), # Convert DayE to calendar days
    log10Population = log10(Population),
    log10Density = log10(Density),
    log10IHRcapacity = log10(IHRcapacity),
    log10Life_expect = log10(Life_expect),
    log10GDP_city = log10(GDP_city),
	Elevation = ifelse(Elevation > 0, Elevation, 1), 
    log10Elevation = log10(Elevation + 1)
  ) # Add 1 before log-transforming for elevation

# Remove columns no longer needed
all <- subset(all, select = -c(GDP_country, Elder_country, Airqual_country, Population, Density, IHRcapacity, Life_expect, GDP_city, Elevation))

# Impute variables (temperature, relative humidity, retail and recreation) based on all other variables
if (analysis != 3) {
  set.seed(1205) # Set seed for reproducibility
  imputed <- all %>%
    select(log10Population, log10Density, Temperature, RH, Daylight, Latitude, log10Elevation, log10GDP_city, Elder_city, Airqual_city, log10Life_expect, log10IHRcapacity, CRD_prev, MeanStringencyIndex_lag2, retail_and_recreation_lag2) %>%
    missForest() %>%
    .$ximp
  all$retail_and_recreation_lag2 <- imputed$retail_and_recreation_lag2
  all$Temperature <- imputed$Temperature
  all$RH <- imputed$RH
}

##################################
# Correlation between covariates #
##################################

# Select variables to exclude
var_for_corr <- within(all, rm("R0", "City", "Country", "DayS", "DayE", "Longitude"))

if (analysis == 3) {
  # Remove constants (country-level data) or NAs
  var_for_corr <- within(var_for_corr, rm("log10GDP_city", "Elder_city", "Airqual_city", "log10Life_expect", "log10IHRcapacity", "CRD_prev", "retail_and_recreation_lag2", "grocery_and_pharmacy_lag2", "parks_lag2", "transit_stations_lag2", "workplace_lag2", "residential_lag2", "MeanStringencyIndex_lag2"))
}

# Calculate pairwise correlations
p.mat <- cor_mtest(var_for_corr, "spearman")
A <- cor(var_for_corr, use = "pairwise.complete.obs", method = "spearman")

# Product correlation plot
png(paste0("corr_plot", suffix, ".png"), height = 1000, width = 1000, res = 120)
corrplot(A, type = "upper", p.mat = p.mat, sig.level = 0.05)
dev.off()

###############################
# Construct regression models #
###############################

# Set model variables
if (analysis != 3) {
  vars <- c("log10Population", "log10Density", "Temperature", "RH", "Daylight", "Latitude", "log10Elevation", "log10GDP_city", "Elder_city", "log10IHRcapacity", "retail_and_recreation_lag2", "MeanStringencyIndex_lag2")
} else if (analysis == 3) {
  vars <- c("log10Population", "log10Density", "Temperature", "RH", "Daylight", "log10Elevation", "MeanStringencyIndex_lag2")
}

# Filter/select final model data
model_data <- all %>%
  mutate(R0 = !!sym(outcome)) %>%
  filter_at(vars(vars, R0), all_vars(complete.cases(.))) %>% # Filter to complete cases in model variables
  select(all_of(vars), R0, City, Country)

if (analysis == 2) {
  model_data <- model_data %>% filter(!(Country == "China"))
} else if (analysis == 3) {
  model_data <- model_data %>% filter(Country == "China")
}

# Construct model formula
model_formula <- as.formula(paste0("R0 ~ ", paste(vars, collapse = "+")))

# Saturated linear regression model
model <- lm(formula = model_formula, model_data)

# Plot model fit
png(paste0("lm", suffix, ".png"))
pl <- ggplot(model_data, aes(x = fitted(model), y = R0, colour = Country)) +
  geom_point() +
  geom_abline(intercept = 0, slope = 1) +
  scale_x_continuous(limits = c(0, ceiling(max(model_data$R0))), expand = c(0, 0)) +
  scale_y_continuous(limits = c(0, ceiling(max(model_data$R0))), expand = c(0, 0)) +
  xlab("Predicted R0") +
  ylab("Calculated R0 from case data") +
  ggtitle("All covariates") +
  theme_bw()
pl + annotate(geom = "text", x = 2.5, y = ceiling(max(model_data$R0)) - 1, label = paste("R² =", round(summary(model)$r.squared, 3)), color = "black")
dev.off()

# Review model diagnostics
summary(model)
coefs <- coef(model)
layout(matrix(c(1, 2, 3, 4), 2, 2))
plot(model)
vif(model)

# Model selection step 1: reduce linear model
step <- stepAIC(model, trace = F, direction = "both")
step$anova

# Plot model fit
png(paste0("lm_aic", suffix, ".png"))
pl <- ggplot(model_data, aes(x = predict(step, model_data), y = R0, colour = Country)) +
  geom_point() +
  geom_abline(intercept = 0, slope = 1) +
  scale_x_continuous(limits = c(0, ceiling(max(model_data$R0))), expand = c(0, 0)) +
  scale_y_continuous(limits = c(0, ceiling(max(model_data$R0))), expand = c(0, 0)) +
  xlab("Predicted r-value") +
  ylab("Calculated r-value from case data") +
  ggtitle(paste0("Covariates picked with AIC:\n", paste(labels(terms(step)), collapse = ", "))) +
  theme_bw()
pl + annotate(geom = "text", x = 2.5, y = ceiling(max(model_data$R0)) - 1, label = paste("R² =", round(summary(step)$r.squared, 3)), color = "black")
dev.off()

# Review model diagnostics
summary(step)
layout(matrix(c(1, 2, 3, 4), 2, 2))
plot(step)
vif(step)

# Model selection step 2: try introducing country-level random effects in a mixed-effects model (only if modelling >1 country)

if (analysis != 3) {
  mixed_mod_step <- lmer(formula = update(formula(step), ~ . + (1 | Country)), data = model_data, na.action = na.omit, REML = FALSE)

  # Likelihood ratio test whether random effects improve model fit
  print(anova(mixed_mod_step, step))

  # Only bother examining the model if it successfully converged
  if (!(isSingular(mixed_mod_step))) {

    # Refit with REML
    mixed_mod_step_reml <- lmer(formula = update(formula(step), ~ . + (1 | Country)), data = model_data, na.action = na.omit, REML = TRUE)

    # Calculate intraclass coefficient
    ranvcov_step <- mixed_mod_step_reml %>%
      VarCorr(comp = c("Variance", "Std.Dev")) %>%
      as.data.frame() %>%
      pull(vcov)
    icc_step <- ranvcov_step[1] / ranvcov_step[2]
    print(icc_step) %>% round(3)

    # Plot model fit
    png(paste0("mem", suffix, ".png"))
    pl <- ggplot(model_data, aes(x = predict(mixed_mod_step_reml, model_data, allow.new.levels = TRUE), y = R0, colour = Country)) +
      geom_point() +
      geom_abline(intercept = 0, slope = 1) +
      scale_x_continuous(limits = c(0, ceiling(max(model_data$R0))), expand = c(0, 0)) +
      scale_y_continuous(limits = c(0, ceiling(max(model_data$R0))), expand = c(0, 0)) +
      xlab("Predicted R0") +
      ylab("Calculated R0 from case data") +
      ggtitle(paste0("Covariates picked with AIC, mixed-effects model:\n", paste(labels(terms(mixed_mod_step_reml)), collapse = ", "))) +
      theme_bw()
    print(pl + annotate(geom = "text", x = 2.5, y = ceiling(max(model_data$R0)) - 1, label = paste("R²_marg =", round(r.squaredGLMM(mixed_mod_step_reml)[1], 3), "\nR²_cond =", round(r.squaredGLMM(mixed_mod_step)[2], 3)), color = "black"))
    dev.off()

    # Review model diagnostics
    print(summary(mixed_mod_step_reml))
    print(vif.mer(mixed_mod_step_reml))
    par(mfrow = c(1, 1))
    plot(mixed_mod_step_reml)
    qqnorm(resid(mixed_mod_step_reml))
    qqline(resid(mixed_mod_step_reml))
  }
}

######################
# Plot model effects #
######################

# Select mixed effects model if fits better by LRT, else select stepwise-reduced fixed effects model
if (analysis != 3) {
  if (unlist(anova(mixed_mod_step, step)["Pr(>Chisq)"])[2] <= 0.05) {
    selected_model <- mixed_mod_step_reml
  } else {
    selected_model <- step
  }
} else {
  selected_model <- step
}

# Identify model variables
selected_vars <- attr(terms(selected_model), "term.labels")

for (i in 1:length(selected_vars)) {

  # Make predictions for range of values for specific variable holding others constant
  pred_df <- suppressMessages(ggpredict(selected_model, terms = selected_vars[i], type = "fe"))
  # Produce effect plot
  fx <- ggplot(pred_df) +
    geom_line(aes(x = x, y = predicted)) +
    geom_ribbon(aes(x = x, ymin = predicted - std.error, ymax = predicted + std.error),
      fill = "lightgrey", alpha = 0.5
    ) +
    geom_point(data = model_data, aes(x = eval(parse(text = selected_vars[i])), y = R0, colour = Country)) +
    xlab(selected_vars[i]) +
    ylab("R0") +
    ggtitle(paste0("Effect plot: ", selected_vars[i])) +
    theme_bw()

  ggsave(fx, file = paste0(i, "_effect", suffix, ".png"), width = 10, height = 6)

  # Additionally, plot on original scale if variable was log-transformed
  if (grepl("log10", selected_vars[i])) {
    fx <- ggplot(pred_df) +
      geom_line(aes(x = 10^x, y = predicted)) +
      geom_ribbon(aes(x = 10^x, ymin = predicted - std.error, ymax = predicted + std.error),
        fill = "lightgrey", alpha = 0.5
      ) +
      geom_point(data = model_data, aes(x = 10^eval(parse(text = selected_vars[i])), y = R0, colour = Country)) +
      xlab(gsub("log10", "", selected_vars[i])) +
      ylab("R0") +
      ggtitle(paste0("Effect plot: ", gsub("log10", "", selected_vars[i]))) +
      theme_bw()

    ggsave(fx, file = paste0(i, "_effect", suffix, "_backtransform.png"), width = 10, height = 6)
  }
}


##########################
# Construct model tables #
##########################

# Construct model table for full model
results_saturated <- data.frame(
  summary(model)$coefficients,
  confint(model)
) %>%
  rownames_to_column("Covariate") %>%
  left_join(model %>%
    drop1(test = "Chisq") %>%
    data.frame() %>%
    rownames_to_column("Covariate"),
  by = "Covariate"
  ) %>%
  filter(Covariate != "(Intercept)") %>%
  mutate(delta_AIC = drop1(model, test = "Chisq")$AIC[1] - AIC)

# Clean and write to table
results_saturated %>%
  rename(t = "t.value", p_t = "Pr...t..", lower_ci = "X2.5..", upper_ci = "X97.5..", p_LRT = "Pr..Chi.") %>%
  select(Covariate, Estimate, t, p_t, lower_ci, upper_ci, delta_AIC, p_LRT) %>%
  mutate_if(is.numeric, round, 3) %>%
  mutate(print_res = paste0(Estimate, " (", lower_ci, ", ", upper_ci, ")")) %>%
  write.csv(paste0("results_saturated", suffix, ".csv"))

# Relative importance: per covariate, saturated fixed-effects model
# Calculate PMVD (Proportional Marginal Variance Decomposition; R^2 contribution averaged over covariate, weighted by data), absolutely and relatively
relimp_df <- bind_cols(
  covar = attr(terms(model), "term.labels"),
  pmvd = calc.relimp.mm(model, rela = FALSE, type = c("pmvd"))$pmvd,
  rel_pmvd = calc.relimp.mm(model, rela = TRUE, type = c("pmvd"))$pmvd
) %>%
  mutate(type = case_when(
    grepl("Temperature|RH|Daylight", covar) ~ "climate",
    grepl("retail_and_recreation|MeanStringencyIndex", covar) ~ "response",
    grepl("Population|Density|Elder_city|Life_expect", covar) ~ "demographic",
    grepl("Elevation|Latitude", covar) ~ "geography",
    grepl("IHRcapacity|GDP_city|Airqual_city|CRD_prev", covar) ~ "socioeconomic"
  ))

# Write to table
relimp_df %>%
  arrange(-pmvd) %>%
  mutate_if(is.numeric, round, 3) %>%
  write.csv(paste0("relaimp_saturated", suffix, ".csv"))

# Relative importance: per covariate category, saturated fixed-effects model
relimp_df %>%
  select(-covar) %>%
  group_by(type) %>%
  summarise_all(sum) %>%
  arrange(-pmvd) %>%
  mutate_if(is.numeric, round, 3) %>%
  write.csv(paste0("relaimp_saturated_type", suffix, ".csv"))


# Construct model table for selected stepwise-reduced model
results_select <- data.frame(
  summary(selected_model)$coefficients,
  confint(selected_model) %>% .[!(rownames(.) %in% c(".sig01", ".sigma")), ]
) %>%
  rownames_to_column("Covariate") %>%
  left_join(selected_model %>%
    drop1(test = "Chisq") %>%
    data.frame() %>%
    rownames_to_column("Covariate"),
  by = "Covariate"
  ) %>%
  filter(Covariate != "(Intercept)")

if (class(selected_model) != "lmerModLmerTest") {
  results_select <- results_select %>% mutate(delta_AIC = drop1(selected_model, test = "Chisq")$AIC[1] - AIC) # Add delta AICs only if not a mixed-effect model
}

# Clean and write to table
results_select %>%
  rename(t = "t.value", p_t = "Pr...t..", lower_ci = "X2.5..", upper_ci = "X97.5..") %>%
  rename_at(vars(matches("^Pr..Chi.$")), function(x) "p_LRT") %>%
  rename_at(vars(matches("^Pr..F.$")), function(x) "p_F") %>%
  select(any_of(c("Covariate", "Estimate", "t", "p_t", "lower_ci", "upper_ci", "delta_AIC", "p_LRT", "p_F"))) %>%
  mutate_if(is.numeric, round, 3) %>%
  mutate(print_res = paste0(Estimate, " (", lower_ci, ", ", upper_ci, ")")) %>%
  write.csv(paste0("results_select", suffix, ".csv"))

# Relative importance: per covariate, selected stepwise-reduced model
# Calculate PMVD (Proportional Marginal Variance Decomposition; R^2 contribution averaged over covariate, weighted by data), absolutely and relatively
relimp_select_df <- bind_cols(
  covar = attr(terms(selected_model), "term.labels"),
  pmvd = calc.relimp.mm(selected_model, rela = FALSE, type = c("pmvd"))$pmvd,
  rel_pmvd = calc.relimp.mm(selected_model, rela = TRUE, type = c("pmvd"))$pmvd
) %>%
  mutate(type = case_when(
    grepl("Temperature|RH|Daylight", covar) ~ "climate",
    grepl("retail_and_recreation|MeanStringencyIndex", covar) ~ "response",
    grepl("Population|Density|Elder_city|Life_expect", covar) ~ "demographic",
    grepl("Elevation|Latitude", covar) ~ "geography",
    grepl("IHRcapacity|GDP_city|Airqual_city|CRD_prev", covar) ~ "socioeconomic"
  ))

# Write to table
relimp_select_df %>%
  arrange(-pmvd) %>%
  mutate_if(is.numeric, round, 3) %>%
  write.csv(paste0("relaimp_select", suffix, ".csv"))

# Relative importance: per covariate category, selected stepwise-reduced model
relimp_select_df %>%
  select(-covar) %>%
  group_by(type) %>%
  summarise_all(sum) %>%
  arrange(-pmvd) %>%
  mutate_if(is.numeric, round, 3) %>%
  write.csv(paste0("relaimp_select_type", suffix, ".csv"))
