#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR/.."

scripts/goose.sh -dir kubernetes ./pkg/api/v1/pod
scripts/goose.sh -dir kubernetes ./pkg/controller
scripts/goose.sh -dir kubernetes ./pkg/controller/replicaset
scripts/goose.sh -dir kubernetes ./pkg/controller/replicaset/metrics
scripts/goose.sh -dir kubernetes ./pkg/features
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/api/core/v1
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/api/apps/v1
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/api/errors
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/api/meta
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/api/resource
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/apis/meta/v1
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/labels
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/runtime/schema
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/types
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/util/runtime
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apimachinery/pkg/util/uuid
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/apiserver/pkg/util/feature
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/client-go/kubernetes
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/client-go/kubernetes/typed/apps/v1
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/client-go/listers/apps/v1
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/client-go/listers/core/v1
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/client-go/tools/cache
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/client-go/util/workqueue
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/component-base/featuregate
scripts/goose.sh -dir kubernetes ./staging/src/k8s.io/component-base/metrics
scripts/goose.sh -dir kubernetes ./vendor/github.com/go-logr/logr
scripts/goose.sh -dir kubernetes ./vendor/k8s.io/klog/v2
scripts/goose.sh -dir kubernetes ./vendor/k8s.io/utils/clock
scripts/goose.sh -dir kubernetes ./vendor/k8s.io/utils/ptr

scripts/goose.sh -dir kubernetes_model ./simplereplicaset
scripts/goose.sh -dir kubernetes_model ./apimodel
