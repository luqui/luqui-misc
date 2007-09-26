package com.learningrx.MotorTapBeat {
	
import com.learningrx.*;
import com.learningrx.Screens.*;

public class MotorTapBeat extends Game {
	
	function MotorTapBeat(pParent:Framework) {
		super(pParent, 'MotorTapBeat', com.learningrx.MotorTapBeat.Turns);

		var avcue = new RhythmGameAVCue(bpmToDelay(120.0), 2);
		avcue.x = BackgroundWidth/2;
		avcue.y = BackgroundHeight/2;
		addChild(avcue);
		avcue.begin();
	}
	
	private static function bpmToDelay(bpm:Number):Number {
		return 60000 / bpm;
	}
	
}
	
}
