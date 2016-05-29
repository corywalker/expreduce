package main

import (
        "container/list"
        "fmt"
        "reflect"
)

func main() {
        // Create a new list and put some numbers in it.
        l := list.New()
        e4 := l.PushBack(4)
        e1 := l.PushFront(1)
        l.InsertBefore(3, e4)
        l.InsertAfter("Hello", e1)

        // Iterate through list and print its contents.
        for e := l.Front(); e != nil; e = e.Next() {
                fmt.Println(e.Value)
                fmt.Println(reflect.TypeOf(e.Value))
                fmt.Println(reflect.TypeOf(e.Value)==int)
                fmt.Println(reflect.TypeOf(e.Value))
        }
        switch v := anything.(type) {
                case string:
                        fmt.Println(v)
                case int32, int64:
                        fmt.Println(v)
                case SomeCustomType:
                        fmt.Println(v)
                default:
                        fmt.Println("unknown")
        }

}
