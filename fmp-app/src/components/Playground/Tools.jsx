import React, { useState } from 'react';
import Options from '../../assets/config/AvailableTools'

import Select from 'react-select';

const Tools = (props) => {
  const [isClearable, setIsClearable] = useState(true);
  const [isSearchable, setIsSearchable] = useState(true);
  const [isDisabled, setIsDisabled] = useState(false);
  const [isLoading, setIsLoading] = useState(false);
  const [isRtl, setIsRtl] = useState(false);
  const [options, setOptions] = useState(Options);

  return (
    <>
      <div style={{ width: '100%', paddingTop: '100px' }}>
        <Select
          className="basic-single"
          classNamePrefix="select"
          defaultValue={options[1]}
          isDisabled={false}
          isLoading={false}
          isClearable={false}
          isRtl={false}
          isSearchable={true}
          name="color"
          options={Options}
          onChange={props.onChange}
        />
      </div>
      <div
        style={{
          color: 'hsl(0, 0%, 40%)',
          display: 'inline-block',
          fontSize: 12,
          fontStyle: 'italic',
          marginTop: '1em',
        }}
      >
      </div>
    </>
  );
};

export default Tools;