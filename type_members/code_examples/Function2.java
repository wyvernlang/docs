interface Equatable <T extends Object >{}

interface List <T extends Object > extends Equatable <List <? extends Equatable <? super T>>>{}

class Tree implements List <Tree >{}

public class Function2 {
    public void func(Equatable<? super Tree> e){
    }

    public static void main(String[] args) {
	Tree t = new Tree ();
	Function2 f = new Function2 ();
 	f.func(t); // BREAK HERE
    }
}

