//go:build ignore

// Run from the Kubernetes module; this helper is not a package of the root
// tooling module.
package main

import (
	"encoding/json"
	"os"
	"reflect"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

type node struct {
	ID     string
	Name   string
	Pkg    string
	Kind   string
	Elem   string
	Key    string
	Fields []field
}
type field struct {
	Name string
	Type string
}

func main() {
	nodes := map[string]node{}
	var order []string
	var visit func(reflect.Type) string
	visit = func(t reflect.Type) string {
		id := t.String()
		if t.Name() != "" {
			id = t.PkgPath() + "/" + t.Name()
		}
		if _, ok := nodes[id]; ok {
			return id
		}
		n := node{ID: id, Name: t.Name(), Pkg: t.PkgPath(), Kind: t.Kind().String()}
		nodes[id] = n
		switch t.Kind() {
		case reflect.Pointer, reflect.Slice, reflect.Array:
			n.Elem = visit(t.Elem())
		case reflect.Map:
			n.Key = visit(t.Key())
			n.Elem = visit(t.Elem())
		case reflect.Struct:
			for i := 0; i < t.NumField(); i++ {
				f := t.Field(i)
				n.Fields = append(n.Fields, field{f.Name, visit(f.Type)})
			}
		}
		nodes[id] = n
		order = append(order, id)
		return id
	}
	roots := map[string][]string{}
	for _, group := range []struct {
		name  string
		types []reflect.Type
	}{
		{"runtime_time", []reflect.Type{reflect.TypeOf(time.Time{})}},
		{"time", []reflect.Type{reflect.TypeOf(metav1.Time{})}},
		{"typemeta", []reflect.Type{reflect.TypeOf(metav1.TypeMeta{})}},
		{"objectmeta", []reflect.Type{reflect.TypeOf(metav1.ObjectMeta{})}},
		{"delete_options", []reflect.Type{reflect.TypeOf(metav1.DeleteOptions{})}},
		{"pod", []reflect.Type{reflect.TypeOf(corev1.Pod{}), reflect.TypeOf(corev1.PodTemplateSpec{})}},
		{"persistentvolumeclaim", []reflect.Type{reflect.TypeOf(corev1.PersistentVolumeClaim{})}},
		{"replicaset", []reflect.Type{reflect.TypeOf(appsv1.ReplicaSet{})}},
		{"statefulset", []reflect.Type{reflect.TypeOf(appsv1.StatefulSet{})}},
		{"deployment", []reflect.Type{reflect.TypeOf(appsv1.Deployment{})}},
	} {
		for _, typ := range group.types {
			roots[group.name] = append(roots[group.name], visit(typ))
		}
	}
	out := struct {
		Nodes map[string]node
		Order []string
		Roots map[string][]string
	}{nodes, order, roots}
	json.NewEncoder(os.Stdout).Encode(out)
}
