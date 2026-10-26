SRC_DIR := 'src'
PROJ_VFILES := $(shell find $(SRC_DIR) -name "*.v")
GENERATED_VFILES := $(filter src/code/% src/generatedproof/% src/generatedviews/%,$(PROJ_VFILES))
CONTROLLER_VFILES := $(filter src/proof/controllers/%,$(PROJ_VFILES))
APIMODEL_VFILES := $(filter src/proof/kubernetes_model/%,$(PROJ_VFILES))
BASE_VFILES := $(filter-out $(GENERATED_VFILES) $(APIMODEL_VFILES) $(CONTROLLER_VFILES),$(PROJ_VFILES))

# This is the single list used by both the CI matrix and the vok targets.
PROOF_GROUPS := generated base apimodel controllers-other \
	controllers-deployment controllers-replicaset controllers-statefulset
PROOF_GROUP_generated := $(GENERATED_VFILES)
PROOF_GROUP_base := $(BASE_VFILES)
PROOF_GROUP_apimodel := $(APIMODEL_VFILES)
PROOF_GROUP_controllers-deployment := $(filter src/proof/controllers/deployment/%,$(CONTROLLER_VFILES))
PROOF_GROUP_controllers-replicaset := $(filter src/proof/controllers/replicaset/%,$(CONTROLLER_VFILES))
PROOF_GROUP_controllers-statefulset := $(filter src/proof/controllers/statefulset/%,$(CONTROLLER_VFILES))
# Include shared helpers and any other or newly added controller directories.
PROOF_GROUP_controllers-other := $(filter-out \
	$(PROOF_GROUP_controllers-deployment) \
	$(PROOF_GROUP_controllers-replicaset) \
	$(PROOF_GROUP_controllers-statefulset),$(CONTROLLER_VFILES))

# Fail before building if the selected groups omit or double-check a file.
GROUPED_VFILES := $(foreach group,$(PROOF_GROUPS),$(PROOF_GROUP_$(group)))
ifneq ($(sort $(PROJ_VFILES)),$(sort $(GROUPED_VFILES)))
$(error Proof groups must cover exactly all PROJ_VFILES)
endif
ifneq ($(words $(GROUPED_VFILES)),$(words $(sort $(GROUPED_VFILES))))
$(error Proof groups must not overlap)
endif

GOOSE_CONFIG_FILES := $(shell find $(SRC_DIR) -name "*.v.toml")
GO_DIR := '.'
GO_FILES := $(shell find $(GO_DIR) -name "*.go")

# extract any global arguments for Rocq from _CoqProject
ROCQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _CoqProject)

# user configurable
Q:=@
ROCQ_ARGS :=
ROCQC := rocq compile
ROCQ_DEP_ARGS := -w +module-not-found

default: vo
.PHONY: default

vo: $(PROJ_VFILES:.v=.vo)
vos: $(PROJ_VFILES:.v=.vos)
vok: $(PROJ_VFILES:.v=.vok)

# CI checks each proof group independently. -vok checks the selected proofs
# while loading .vos dependencies, including imports from other proof groups.
vo-base: $(BASE_VFILES:.v=.vo)
vos-base: $(BASE_VFILES:.v=.vos)
$(foreach group,$(PROOF_GROUPS),$(eval vok-$(group): $(PROOF_GROUP_$(group):.v=.vok)))
# Keep the aggregate controller target available for local checks.
vok-controllers: $(CONTROLLER_VFILES:.v=.vok)
.PHONY: vo vos vok vo-base vos-base vok-controllers $(addprefix vok-,$(PROOF_GROUPS))

# Listing groups also runs the coverage checks above, without needing Rocq.
proof-groups:
	@python3 -c 'import json; print(json.dumps("$(PROOF_GROUPS)".split()))'
.PHONY: proof-groups

.goose-output: $(GO_FILES) $(GOOSE_CONFIG_FILES) goose.toml
	@echo "GOOSE"
	$(Q)go tool perennial-cli goose --config goose-kubernetes-model.toml
	$(Q)go tool perennial-cli goose --config goose-kubernetes.toml
	@touch $@

.rocqdeps.d: $(PROJ_VFILES) _CoqProject
	@echo "ROCQ dep $@"
	$(Q)rocq dep $(ROCQ_DEP_ARGS) -vos -f _CoqProject $(PROJ_VFILES) > $@

# Metadata-only invocations must work before Rocq is installed in CI.
# Mixed invocations with a proof target still need the dependency file.
ifneq ($(MAKECMDGOALS),)
SKIP_ROCQ_DEPS := $(if $(filter-out clean proof-groups,$(MAKECMDGOALS)),,1)
endif
ifeq ($(SKIP_ROCQ_DEPS),)
-include .rocqdeps.d
endif

%.vo: %.v _CoqProject | .rocqdeps.d
	@echo "ROCQ compile $<"
	$(Q)$(ROCQC) $(ROCQPROJECT_ARGS) $(ROCQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject | .rocqdeps.d
	@echo "ROCQ -vos $<"
	$(Q)$(ROCQC) $(ROCQPROJECT_ARGS) -vos $(ROCQ_ARGS) $< -o $@

%.vok: %.v _CoqProject | .rocqdeps.d
	@echo "ROCQ -vok $<"
	$(Q)$(ROCQC) $(ROCQPROJECT_ARGS) -vok $(ROCQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIR) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
# 	$(Q)for dir in $(SRC_DIR)/code $(SRC_DIR)/generatedproof; do \
# 		if test -d "$$dir"; then find "$$dir" -name "*.v" -delete; fi \
	done
	$(Q)rm -f .goose-output
	$(Q)rm -f .rocqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
