package com.learningrx.MotorTapBeat {

import flash.display.MovieClip;

public class Blinker extends MovieClip {
	function Blinker() {
		turnOff();
	}
	
	public function turnOff():void {
		gotoAndStop('off');
	}
	
	public function turnRed():void {
		gotoAndStop('red');
	}
	
	public function turnGreen():void {
		gotoAndStop('green');
	}
}

}
