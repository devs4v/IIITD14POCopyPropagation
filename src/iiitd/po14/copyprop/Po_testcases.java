import java.util.Scanner;

//import java.util.*;
public class Po_testcases {
	public static void main(String args[])
	{
		int res=0;
		Scanner sc=new Scanner(System.in);
	    int x=sc.nextInt();
	    int y=sc.nextInt();
	    int z=sc.nextInt();
	    Po_testcases ob=new Po_testcases();
	    if(x>100)
	    {
	    	res=ob.calc(y,z);
	    }
		System.out.println("value of d is "+res);
	}
	public int calc(int y, int z)
	{
		int a = y;
		int b = a-z;
		int d = b;
		return  d;
	}
}
