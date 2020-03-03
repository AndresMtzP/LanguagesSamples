import java.util.concurrent.atomic.AtomicLongArray;

class AcmeSafeState implements State {
    private AtomicLongArray value;

    AcmeSafeState(int length) { value = new AtomicLongArray(length); }

    public int size() { return value.length(); }

    public long[] current() {  
    	long[] placeholder = new long[size()];
    	for(int i = 0; i < value.length(); i++)
    	{
    		placeholder[i] = value.get(i);
    	} 
    	return placeholder;
    }

    public void swap(int i, int j) {
	value.getAndDecrement(i);
	value.getAndIncrement(j);
    }
}