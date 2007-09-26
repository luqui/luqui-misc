package com.learningrx.MotorTapBeat {
	
import flash.display.MovieClip;

public class MotorTapBeat extends MovieClip {
	
	function MotorTapBeat() {
		var avcue = new RhythmGameAVCue(bpmToDelay(120.0), 2);
		avcue.x = stage.stageWidth/2;
		avcue.y = stage.stageHeight/2;
		addChild(avcue);
		avcue.begin();
	}
	
	private static function bpmToDelay(bpm:Number):Number {
		return 60000 / bpm;
	}
	
}
	
}
