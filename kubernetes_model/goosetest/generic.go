package goosetest

type foo interface {
	FooNum() int
}

type bar interface {
	BarNum() int
}

type Foo[T foo] struct {
	newFoo func() T
}

type alsoBar[T1 foo, T2 bar] struct {
	obj    *Foo[T1]
	newBar func() T2
}

func (o *Foo[T]) A(obj T) (T, int) {
	return o.newFoo(), obj.FooNum()
}

func (o *alsoBar[T1, T2]) B(obj1 T1, obj2 T2) (T1, T2, int) {
	return o.obj.newFoo(), o.newBar(), obj1.FooNum() + obj2.BarNum()
}
