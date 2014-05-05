package iiitd.po14.copyprop;

import java.util.*;


public class TestCases {

	public int calc(int y, int z)
	{
		int a = y;
		int b = a-z;
		int d = b;
		return  d;
	}
	public static void main(String[] args) {
		
		
		int res=0;
		Scanner sc=new Scanner(System.in);
	    int x=sc.nextInt();
	    int y=sc.nextInt();
	    int z=sc.nextInt();
	    TestCases ob=new TestCases();
	    if(x>100)
	    {
	    	res=ob.calc(y,z);
	    }
		System.out.println("value of d is "+res);
	}
	


	}


