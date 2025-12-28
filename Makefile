SRC_DIR := 'src'
PROJ_VFILES := $(shell find $(SRC_DIR) -name "*.v")
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

.goose-output: $(GO_FILES) $(GOOSE_CONFIG_FILES) goose.toml
	@echo "GOOSE"
	$(Q)go tool perennial-cli goose --config goose-kubernetes-model.toml
	$(Q)go tool perennial-cli goose --config goose-kubernetes.toml
	@touch $@

.rocqdeps.d: $(PROJ_VFILES) _CoqProject
	@echo "ROCQ dep $@"
	$(Q)rocq dep $(ROCQ_DEP_ARGS) -vos -f _CoqProject $(PROJ_VFILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
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
