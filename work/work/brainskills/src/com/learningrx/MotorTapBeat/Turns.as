package com.learningrx.MotorTapBeat
{

import com.learningrx.*;

public class Turns
{
	private static var _Game:Game;
	public static function set Game(pGame:Game):void
	{
		_Game = pGame;
	}

	public static function GetLevelsAndSublevels():Object
	{
		var sublevels:Object = new Object();
		sublevels.NumberOfLevels = NumberOfLevels;
		sublevels[1] = 1;
		return sublevels;
	}

	public static function get NumberOfLevels():Number
	{
		return 1;
	}
}

}
