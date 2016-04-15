interface Equatable <T extends Object >{}

interface List <T extends Object > extends Equatable <List <? extends Equatable <? super T>>>{}

class ArrayList<T extends Object> implements List<T>{}

class Tree extends ArrayList <Tree >{}

public class Function {
    public void func(Equatable<? super Tree> e){
    }

    public static void main(String[] args) {
	Tree t = new Tree (); Function f = new Function ();
	f.func(t);
    }
}

