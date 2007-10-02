package com.learningrx.MotorTapBeat {
	
import flash.media.Sound;
import flash.media.SoundTransform;

public class RhythmGameVolumeHearing extends RhythmGameQueue {
	
	private var m_volumes:Array = [0.1, 0.5, 1.0];
	private var m_sound:Sound = new ToneG4Norm();
	
	function RhythmGameVolumeHearing(game:MotorTapBeat, interval:Number) {
		super(game, interval);
	}
	
	protected override function subOnHit(beat:int, prev2:Object, prev1:Object, dir:String):Boolean {
		return prev1 > prev2 && dir == "up" || prev1 < prev2 && dir == "down";
	}
	
	protected override function pickIndex(prev:Object):Object {
		var index = 0;
		do {
			index = int(Math.random() * m_volumes.length);
		} while (index == prev);
		return index;
	}
	
	protected override function playIndex(idx:Object):void {
		m_sound.play(0, 0, new SoundTransform(m_volumes[idx]));
	}
}

}