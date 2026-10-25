//go:build ignore

// generate_views.py runs this helper from the Kubernetes module together with
// a temporary main function selecting the configured root types.
package main

import (
	"encoding/json"
	"os"
	"reflect"
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

type rootGroup struct {
	name  string
	types []reflect.Type
}

func extractSchema(groups []rootGroup) {
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
	for _, group := range groups {
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
