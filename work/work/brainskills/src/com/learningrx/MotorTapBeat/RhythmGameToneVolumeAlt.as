package com.learningrx.MotorTapBeat {
	
import flash.media.Sound;
import flash.media.SoundTransform;
import flash.utils.getDefinitionByName;

public class RhythmGameToneVolumeAlt extends RhythmGameQueue {
	
	private var m_volumes:Array = [0.1, 0.5, 1.0];
	private var m_tones:Array;
	
	function RhythmGameToneVolumeAlt(game:MotorTapBeat, interval:Number) {
		super(game, interval);
		
		m_tones = [];
		for each (var i:String in ["C3", "G3", "C4", "G4", "C5", "G5"]) {
			var prefix:String = "com.learningrx.MotorTapBeat.Tone" + i;
			var tone = new (getDefinitionByName(prefix + "Norm") as Class)();
			m_tones.push(tone);
		}
	}
	
	protected override function subOnHit(beat:int, prev2:Object, prev1:Object, dir:String):Boolean {
		if (beat % 2 == 0) {
			return prev1.tone > prev2.tone && dir == "up" || prev1.tone < prev2.tone && dir == "down";
		}
		else {
			return prev1.vol  > prev2.vol  && dir == "up" || prev1.vol  < prev2.vol  && dir == "down";
		}
	}
	
	protected override function pickIndex(prev:Object):Object {
		var index;
		do {
			index = { 
				tone: int(Math.random() * m_tones.length), 
				vol:  int(Math.random() * m_volumes.length)
			};
		} while (prev != null && (index.tone == prev.tone || index.vol == prev.vol));
		return index;
	}
	
	protected override function playIndex(idx:Object):void {
		m_tones[idx.tone].play(0, 0, new SoundTransform(m_volumes[idx.vol]));
	}
}

}