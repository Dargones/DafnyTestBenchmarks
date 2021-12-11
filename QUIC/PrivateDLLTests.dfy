include "PrivateDLL.dfy"

module PrivateDLLTests {

    import opened PrivateDLL

    // The two methods below have to be implemented in the target language

    method {:extern} GetFreshPrivateDoublyLinkedList<T>() 
        returns (list:PrivateDoublyLinkedList<T>) 
        ensures fresh(list)

    method {:extern} GetFreshPrivateNode<T>() 
        returns (node:PrivateNode<T>) 
        ensures fresh(node)

    // The four helper methods below help to avoid repetition.
    // While these can be merged into one method, I split them for readability

    method GetEmptyList<T> ()
        returns (list:PrivateDoublyLinkedList<T>)
        ensures fresh(list) 
        ensures list.Repr == {} && list.Valid()
    {
        list := GetFreshPrivateDoublyLinkedList<T>();
        list.Nodes := [];
        list.Repr := {};
        list.Vals := [];
        list.head := null;
        list.tail := null;
    }

    method GetListWithOneNode<T> (payload:T)
        returns (list:PrivateDoublyLinkedList<T>, node:PrivateNode<T>)
        ensures fresh(list) && fresh(node)
        ensures list.Repr == {node} && list.Valid()
    {
        node := GetFreshPrivateNode<T>();
        list := GetFreshPrivateDoublyLinkedList<T>();
        node.payload := payload;
        node.L := null;
        node.R := null;
        list.Nodes := [node];
        list.Repr := {node};
        list.Vals := [payload];
        list.head := node;
        list.tail := node;
    }

    method GetListWithTwoNodes<T> (payload1:T, payload2:T)
        returns (list:PrivateDoublyLinkedList<T>, 
                 node1:PrivateNode<T>,
                 node2:PrivateNode<T>)
        ensures fresh(list) && fresh(node1) && fresh(node2)
        ensures list.Repr == {node1, node2} && list.Nodes == [node1, node2]
        ensures list.Valid()
    {
        node1 := GetFreshPrivateNode<T>();
        node2 := GetFreshPrivateNode<T>();
        list := GetFreshPrivateDoublyLinkedList<T>();
        node1.payload := payload1;
        node1.L := null;
        node1.R := node2;
        node2.payload := payload2;
        node2.L := node1;
        node2.R := null;
        list.Nodes := [node1, node2];
        list.Repr := {node1, node2};
        list.Vals := [payload1, payload2];
        list.head := node1;
        list.tail := node2;
    }

    method GetListWithThreeNodes<T> (payload1:T, payload2:T, payload3:T)
        returns (list:PrivateDoublyLinkedList<T>, 
                 node1:PrivateNode<T>,
                 node2:PrivateNode<T>,
                 node3:PrivateNode<T>)
        ensures fresh(list) && fresh(node1) && fresh(node2) && fresh(node3)
        ensures list.Repr == {node1, node2, node3}
        ensures list.Nodes == [node1, node2, node3]
        ensures list.Valid()
    {
        node1 := GetFreshPrivateNode<T>();
        node2 := GetFreshPrivateNode<T>();
        node3 := GetFreshPrivateNode<T>();
        list := GetFreshPrivateDoublyLinkedList<T>();
        node1.payload := payload1;
        node1.L := null;
        node1.R := node2;
        node2.payload := payload2;
        node2.L := node1;
        node2.R := node3;
        node3.payload := payload3;
        node3.L := node2;
        node3.R := null;
        list.Nodes := [node1, node2, node3];
        list.Repr := {node1, node2, node3};
        list.Vals := [payload1, payload2, payload3];
        list.head := node1;
        list.tail := node3;
    }

    // Below are the tests proper

    method TestIsEmptyTrue() {
        var list := GetEmptyList<int>();    
        var empty := list.IsEmpty();
        // expect empty;
    }

    method TestIsEmptyFalse() {
        var list, _ := GetListWithOneNode<int>(5);
        var empty := list.IsEmpty();
        // expect !empty;
    }

    method TestRemoveOnly() {
        var list, node := GetListWithOneNode<int>(5);
        var _ := list.Remove(node);
    }

    method TestRemoveFirst() {
        var list, head, _ := GetListWithTwoNodes<int>(5, 6);
        var _ := list.Remove(head);
    }

    method TestRemoveLast() {
        var list, _, tail := GetListWithTwoNodes<int>(5, 6);
        var _ := list.Remove(tail);
    }

    method TestRemoveMiddle() {
        var list, _, node, _ := GetListWithThreeNodes<int>(5, 6, 7);
        var _ := list.Remove(node);
    }

    method TestRemoveHead() {
        var list, _, _ := GetListWithTwoNodes<int>(5, 6);
        var head := list.RemoveHead();
        // expect head == 5;
    }

    method TestRemoveTail() {
        var list, _, _ := GetListWithTwoNodes<int>(5, 6);
        var tail := list.RemoveTail();
        // expect tail == 6;
    }

    method TestInsertHeadEmpty() {
        var list := GetEmptyList<int>();    
        list.InsertHead(5);
    }

    method TestInsertHeadNonEmpty() {
        var list, _ := GetListWithOneNode<int>(6);
        list.InsertHead(5); 
    }

    method TestInsertTailEmpty() {
        var list := GetEmptyList<int>();    
        list.InsertTail(5);
    }

    method TestInsertTailNonEmpty() {
        var list, _ := GetListWithOneNode<int>(6);
        list.InsertTail(5); 
    }

    method TestPeekHead() {
        var list, _, _ := GetListWithTwoNodes<int>(3, 4);    
        var head := list.PeekHead();
        // expect head == 3;
    }

    method TestPeekTail() {
        var list, _, _ := GetListWithTwoNodes<int>(3, 4);    
        var tail := list.PeekTail();
        // expect tail == 4;
    }

    method TestClear() {
        var list, _, _ := GetListWithTwoNodes<int>(3, 4);    
        list.Clear();
    }


}