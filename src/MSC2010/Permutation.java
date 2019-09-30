import java.util.ArrayList;
import java.util.List;
import java.util.Collections;
import java.lang.ref.WeakReference;

public class Permutation {

    static final int MAX_CACHE_PERM = 6;

    static private List<List<Permutation>> arrayOfAllPerms
    	= new ArrayList<List<Permutation>>();

	private List<Byte> table;
	private boolean isIdentity;
	private WeakReference<Permutation> knownInverse;
	
	private Permutation(
		List<Byte> aTable, boolean skipTest, boolean isIdentity
	) {
	    this.table = aTable;
	    this.isIdentity = skipTest ? isIdentity : testForIdentity(aTable);
	    this.knownInverse = null;
	}
	
	private Permutation(List<Byte> aTable) {
	    this(aTable, false, false);
	}
	
	public String permuteString(String s) {
	    int n = table.size();
	    if ( s.length() != n ) {
	        throw new RuntimeException(
	        	"Only strings of length " + n
	        	+ " can be used with this method"
	        );
	    }
	    StringBuffer sb = new StringBuffer(n);
	    for (Byte b : table) {
	        sb.append(s.charAt(b.intValue()));
	    }
	    return sb.toString();
	}
	
	public String toString() {
		return toString(this.table);
	}
	
	// Static public methods
	

	static public List<Permutation> allPermutations(int n) {
		if ( 0 <= n && n < arrayOfAllPerms.size() ) {
		    List<Permutation> all0 =  arrayOfAllPerms.get(n);
		    if ( all0 != null ) {
		    	return all0;
		    }
		}
		List<List<Byte>> x = allPermutations0(n);
		List<Permutation> all = new ArrayList<Permutation>();
		boolean isIdentity = true;
		for( List<Byte> lb : x) {
		    all.add(new Permutation(lb, true, isIdentity));
		    isIdentity = false;
		}
		all = Collections.unmodifiableList(all);
		if (  0 <= n && n <= MAX_CACHE_PERM ) {
		    while ( arrayOfAllPerms.size() <= n ) {
		    	arrayOfAllPerms.add(null);
		    }
		    arrayOfAllPerms.set(n, all);
		}
		return all;
	}
	
	// Internals
	
	private static boolean testForIdentity(List<Byte> aTable) {
	    int n = aTable.size();
	    for(int i = 0; i < n; i ++) {
	        if( aTable.get(i).intValue() != i ) {
	        	return false;
	        }
	    }
	    return true;
	}
	
	private static String toString(List<Byte> aTable) {
	    StringBuffer sb = new StringBuffer(aTable.size());
	    for ( Byte b : aTable) {
	        sb.append(b);
	    }
	    return sb.toString();
	}

    private static List<List<Byte>> allPermutations0(
    	List<List<Byte>> starts, Byte ... remainder
    ) {
        if ( remainder.length == 0 ) {
            return starts;
        }
        List<List<Byte>> accumulator = new ArrayList<List<Byte>>();
        if ( remainder.length == 1 ) {
            for( Byte b : remainder ) {
                for( List<Byte> start : starts ) {
                        List<Byte> copiedList
                        	= new ArrayList<Byte>(start);
                        copiedList.add(b);
                        accumulator.add(copiedList);
                }
            }
        } else {
            int n = remainder.length;
            for( int i = 0; i < n; i ++) {
                Byte b = remainder[i];
                Byte[] copiedRemainder = new Byte[n-1];
                for(int j = 0, k = 0; j < n; j ++ ) {
                    if ( j != i ) {
                        copiedRemainder[k] = remainder[j];
                        k++;
                    }
                }
                List<List<Byte>> intermediateAccumulator
                	= new ArrayList<List<Byte>>();
                for( List<Byte> start : starts ) {
                        List<Byte> copiedList
                        	= new ArrayList<Byte>(start);
                        copiedList.add(b);
                        intermediateAccumulator.add(copiedList);
                }
                accumulator.addAll(
                	allPermutations0(
                		intermediateAccumulator, copiedRemainder
                	)
                );
            }
        }
        return accumulator;
    }

    private static List<List<Byte>> allPermutations0(int n) {
        if ( n < 0 || n > 12 ) {
            throw new RuntimeException(
            	"n(" + n + ") is out of range 0..12"
            );
        }
        
        Byte[] labels = new Byte[n];
        for (int i = 0; i < n; i ++ ) {
                labels[i] = new Byte((byte)i);
        }
        List<List<Byte>> starts = new ArrayList<List<Byte>>();
        starts.add(new ArrayList<Byte>());
        
        List<List<Byte>> x = allPermutations0(starts, labels);
        
        return x;
    }

    public static void main(String[] args) {
        for( int i = 0; i <= 10 ; i ++ ) {
            List<Permutation> x = allPermutations(i);
            
            for ( Permutation p : x ) {
            	System.out.println(p);
            	System.out.println(
            		p.permuteString("ABCDEFGHIJ".substring(0,i))
            	);
        	}
        	System.out.println(i +  " -> Size = " + x.size());
        }
    }

}
