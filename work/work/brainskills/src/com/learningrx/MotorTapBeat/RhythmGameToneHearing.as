package com.learningrx.MotorTapBeat {
	
import flash.media.Sound;
import flash.utils.getDefinitionByName;

public class RhythmGameToneHearing extends RhythmGameQueue {
	
	private var m_tones:Array;
	
	function RhythmGameToneHearing(game:MotorTapBeat, interval:Number) {
		super(game, interval);
		
		m_tones = [];
		for each (var i:String in ["C3", "G3", "C4", "G4", "C5", "G5"]) {
			var prefix:String = "com.learningrx.MotorTapBeat.Tone" + i;
			var tone = new (getDefinitionByName(prefix + "Norm") as Class)();
			m_tones.push(tone);
		}
	}

	protected override function subOnHit(beat:int, prev2:Object, prev1:Object, dir:String):Boolean {
		return prev1 > prev2 && dir == "up" || prev1 < prev2 && dir == "down";
	}
	
	protected override function pickIndex(prev:Object):Object {
		var idx = 0;
		do {
			idx = int(Math.random() * m_tones.length);
		} while (idx == prev);
		return idx;
	}
	
	protected override function playIndex(idx:Object):void {
		m_tones[idx].play();
	}
}

}