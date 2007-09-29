package com.learningrx.MotorTapBeat {
	
import com.learningrx.*;
import com.learningrx.Screens.*;

public class MotorTapBeat extends Game {
	
	private var m_avcue:RhythmGameAVCue;
	
	function MotorTapBeat(pParent:Framework) {
		super(pParent, 'MotorTapBeat', com.learningrx.MotorTapBeat.Turns);
	}
	
	public override function OnStartRoundButtonClicked():void {
		m_avcue = new RhythmGameAVCue(bpmToDelay(120.0), 2);
		m_avcue.x = BackgroundWidth/2;
		m_avcue.y = BackgroundHeight/2;
		addChild(m_avcue);
		m_avcue.begin()
	}
	
	public override function ResetEverything():void {
		if (m_avcue != null) {
			removeChild(m_avcue);
			m_avcue.end();
			m_avcue = null;
		}
	}
	
	private static function bpmToDelay(bpm:Number):Number {
		return 60000 / bpm;
	}
	
}
	
}
